package alpine
package parsing

import alpine.ast
import alpine.util.FatalError

import scala.annotation.tailrec
import scala.collection.mutable
import scala.collection.SeqView.Reverse

class Parser(val source: SourceFile):

  import ast.*
  import Token.Kind as K

  /** The token stream. */
  private var tokens = Lexer(source)

  /** The boundary of the last consumed token. */
  private var lastBoundary = 0

  /** The next token in the stream if it has already been produced. */
  private var lookahead: Option[Token] = None

  /** The errors collected by the parser. */
  private var errors = mutable.ListBuffer[SyntaxError]()

  /** A stack of predicates identifying tokens suitable for error recovery. */
  private var recoveryPredicates = mutable.ListBuffer[Token => Boolean]()

  /** The diagnostics collected by the parser. */
  def diagnostics: DiagnosticSet =
    DiagnosticSet(errors)

  // --- Declarations ---------------------------------------------------------

  /** Parses and returns a program. */
  def program(): alpine.Program =
    @tailrec def loop(partialResult: List[Declaration]): IArray[Declaration] =
      if peek != None then
        loop(partialResult :+ topLevel())
      else
        IArray.from(partialResult)
    Program(loop(List()))

  /** Parses and returns a top-level declaration. */
  def topLevel(): Declaration =
    peek match
      case Some(Token(K.Let, _)) =>
        binding()
      case Some(Token(K.Fun, _)) =>
        function()
      case Some(Token(K.Type, _)) =>
        typeDeclaration()
      case _ =>
        recover(ExpectedTree("top-level declaration", emptySiteAtLastBoundary), ErrorTree.apply)

  /** Parses and returns a binding declaration. */
  private[parsing] def binding(initializerIsExpected: Boolean = true): Binding =
    val start = lastBoundary
    if (take(K.Let) == None) report(ExpectedTokenError(K.Case, emptySiteAtLastBoundary))
    val iden = identifier()
    val ascription = take(K.Colon).map((_) => tpe())
    val init = take(K.Eq) match {
      case Some(_) => Some(expression())
      case None =>
        if (initializerIsExpected) report(SyntaxError("Initializer Expected", source.span(lastBoundary, lastBoundary)))
        None
    }
    val end = lastBoundary
    Binding(iden.value, ascription, init, source.span(start, end))

  /** Parses and returns a function declaration. */
  private[parsing] def function(): Function =
    val start = lastBoundary
    val s = expect(K.Fun)
    val i = functionIdentifier()
    val params = valueParameterList()
    val output: Option[Type] = take(K.Arrow) match {
      case Some(_) => Some(tpe())
      case None => None
    }
    val body = functionBody()
    val end = lastBoundary
    Function(i, Nil, params, output, body, source.span(start, end))

  /** Parses and returns the identifier of a function. */
  private def functionIdentifier(): String =
    take(K.Identifier) match
      case Some(s) =>
        s.site.text.toString
      case _ if peek.map((t) => t.kind.isOperatorPart).getOrElse(false) =>
        operatorIdentifier()(1).text.toString
      case _ =>
        missingName

  /** Parses and returns a list of parameter declarations in parentheses. */
  private[parsing] def valueParameterList(): List[Parameter] =
    inParentheses(() => commaSeparatedList(K.RParen.matches, parameter)).collect({ case p: Parameter => p })

  /** Parses and returns a parameter declaration. */
  private[parsing] def parameter(): Declaration =
    val start = lastBoundary
    val label = take(K.Underscore) match {
      case Some(_) => None
      case None => take()
    }

    val iden = peek.filter(K.Identifier.matches) match {
      case Some(i) => identifier()
      case _ => Identifier(label.map(_.site.text.toString).getOrElse(""), label.map(_.site).getOrElse(source.span(start, lastBoundary)))
    }

    val ascription = take(K.Colon) match {
      case Some(_) => Some(tpe())
      case None => None
    }
    val end = lastBoundary

    Parameter(label.map(_.site.text.toString), iden.value, ascription, source.span(start, end))

  private def functionBody(): Expression =
    inBraces(expression)

  /** Parses and returns a type declaration. */
  private[parsing] def typeDeclaration(): TypeDeclaration =
    val start = lastBoundary
    val s = expect(K.Type)
    val iden = typeIdentifier()
    val t = expect(K.Eq)
    val u = tpe()
    val end = lastBoundary
    TypeDeclaration(iden.value, Nil, u, source.span(start, end))

  /** Parses and returns a list of parameter declarations in angle brackets. */
  //--- This is intentionally left in the handout /*+++ +++*/
  private def typeParameterList(): List[Parameter] =
    inAngles(() => commaSeparatedList(K.RAngle.matches, parameter))
      .collect({ case p: Parameter => p })

  // --- Expressions ----------------------------------------------------------

  /** Parses and returns a term-level expression. */
  def expression(): Expression =
    infixExpression()

  /** Parses and returns an infix expression. */
  private[parsing] def infixExpression(precedence: Int = ast.OperatorPrecedence.min): Expression =
    val start = lastBoundary
    infixRecur(ascribed(), start, precedence)

  private def infixRecur(lhs: Expression, start: Int, precedence: Int): Expression =
    peek.filter(p => K.Operator.matches(p) || K.Eq.matches(p)) match {
      case Some(_) =>
        operatorIdentifier() match {
          case (Some(op), p1) if (op.precedence >= precedence) =>
            val opIden = Identifier(p1.text.toString, p1)
            val rhs = ascribed()

            val exp = InfixApplication(opIden, lhs, rhs, source.span(start, lastBoundary))
            peek.filter(K.Operator.matches) match {
              case Some(_) =>
                val snap = snapshot()
                operatorIdentifier() match {
                  case (Some(nextOp), p2) =>
                    if (nextOp.precedence > op.precedence)
                      restore(snap)
                      val r = infixRecur(rhs, rhs.site.start, op.precedence + 1)
                      InfixApplication(opIden, lhs, r, source.span(start, lastBoundary))
                    else
                      restore(snap)
                      infixRecur(exp, start, precedence)
                  case _ => InfixApplication(opIden, lhs, rhs, source.span(start, lastBoundary))
                }

              case None => exp
            }

          case _ =>
            lhs
        }
      case None =>
        lhs
    }


  /** Parses and returns an expression with an optional ascription. */
  private[parsing] def ascribed(): Expression =
    val start = lastBoundary
    val prefix = prefixExpression()
    typecast() match {
      case Some(Typecast.Widen) =>
        AscribedExpression(prefix, Typecast.Widen, tpe(), source.span(start, lastBoundary))
      case Some(Typecast.NarrowUnconditionally) =>
        AscribedExpression(prefix, Typecast.NarrowUnconditionally, tpe(), source.span(start, lastBoundary))
      case Some(Typecast.Narrow) =>
        AscribedExpression(prefix, Typecast.Narrow, tpe(), source.span(start, lastBoundary))
      case None => prefix
    }

  /** Parses and returns a prefix application. */
  private[parsing] def prefixExpression(): Expression =
    val start = lastBoundary
    val snap = snapshot()
    takeIf(_.kind.isOperatorPart) match {
      case Some(t) =>
        restore(snap)
        operator() match {
          case op: Identifier =>
            if (noWhitespaceBeforeNextToken)
              val arg = compoundExpression()
              PrefixApplication(op, arg, source.span(start, lastBoundary))
            else op
          case e => throw FatalError("expected operator", e.site)
        }

      case None => compoundExpression()
    }

  /** Parses and returns a compound expression. */
  private[parsing] def compoundExpression(): Expression =
    val start = lastBoundary
    val qualification = primaryExpression()

    take(K.Dot) match {
      case Some(_) =>  {
        val exp = compoundExpression()
        val end = lastBoundary
        exp match {
          case e: Selectee => Selection(qualification, e, source.span(start, end))
          case _ => throw FatalError("expected selectee", exp.site)
        }
      }
      case None =>
        peek.map(K.LParen.matches) match {
          case Some(true) => {
            val params = parenthesizedLabeledList(expression)
            Application(qualification, params, source.span(start, lastBoundary))
          }
          case _ => qualification
        }
    }

  /** Parses and returns a term-level primary exression.
   *
   *  primary-expression ::=
   *    | value-identifier
   *    | integer-literal
   *    | float-literal
   *    | string-literal
   */
  private[parsing] def primaryExpression(): Expression =
    peek match
      case Some(Token(K.Identifier, s)) =>
        identifier()
      case Some(Token(K.True, _)) =>
        booleanLiteral()
      case Some(Token(K.False, _)) =>
        booleanLiteral()
      case Some(Token(K.Integer, _)) =>
        integerLiteral()
      case Some(Token(K.Float, _)) =>
        floatLiteral()
      case Some(Token(K.String, _)) =>
        stringLiteral()
      case Some(Token(K.Label, _)) =>
        recordExpression()
      case Some(Token(K.If, _)) =>
        conditional()
      case Some(Token(K.Match, _)) =>
        mtch()
      case Some(Token(K.Let, _)) =>
        let()
      case Some(Token(K.LParen, _)) =>
        lambdaOrParenthesizedExpression()
      case Some(t) if t.kind.isOperatorPart =>
        operator()
      case _ =>
        recover(ExpectedTree("expression", emptySiteAtLastBoundary), ErrorTree.apply)

  /** Parses and returns an Boolean literal expression. */
  private[parsing] def booleanLiteral(): BooleanLiteral =
    val s = expect("Boolean literal", K.True | K.False)
    BooleanLiteral(s.site.text.toString, s.site)

  /** Parses and returns an integer literal expression. */
  private[parsing] def integerLiteral(): IntegerLiteral =
    val s = expect(K.Integer)
    IntegerLiteral(s.site.text.toString, s.site)

  /** Parses and returns a floating-point literal expression. */
  private[parsing] def floatLiteral(): FloatLiteral =
    val s = expect(K.Float)
    FloatLiteral(s.site.text.toString, s.site)

  /** Parses and returns a string literal expression. */
  private[parsing] def stringLiteral(): StringLiteral =
    val s = expect(K.String)
    StringLiteral(s.site.text.toString, s.site)

  /** Parses and returns a term-level record expression. */
  private def recordExpression(): Record =
    record(recordExpressionFields, Record.apply)

  /** Parses and returns the fields of a term-level record expression. */
  private def recordExpressionFields(): List[Labeled[Expression]] =
    parenthesizedLabeledList(expression)

  /** Parses and returns a conditional expression. */
  private[parsing] def conditional(): Expression =
    val start = lastBoundary
    val s = expect(K.If)
    val condition = expression()

    val t = expect(K.Then)
    val successCase = expression()

    val u = expect(K.Else)
    val failureCase = expression()
    val end = lastBoundary

    Conditional(condition, successCase, failureCase, source.span(start, end))


  /** Parses and returns a match expression. */
  private[parsing] def mtch(): Expression =
    val start = lastBoundary
    expect(K.Match)
    val exp = expression()
    val body = matchBody()
    Match(exp, body, source.span(start, lastBoundary))

  /** Parses and returns a the cases of a match expression. */
  private def matchBody(): List[Match.Case] =
    @tailrec def loop(partialResult: List[Match.Case]): List[Match.Case] =
      peek match
        case Some(Token(K.RBrace, _)) =>
          partialResult
        case Some(Token(K.Case, _)) =>
          loop(partialResult :+ matchCase())
        case _ =>
          report(ExpectedTokenError(K.Case, emptySiteAtLastBoundary))
          discardUntilRecovery()
          if peek == None then partialResult else loop(partialResult)
    inBraces({ () => recovering(K.Case.matches, () => loop(List())) })

  /** Parses and returns a case in a match expression. */
  private def matchCase(): Match.Case =
    val s = peek.map((t) => t.site)
    if take(K.Case) == None then
      report(ExpectedTokenError(K.Case, emptySiteAtLastBoundary))
    val p = pattern()
    if take(K.Then) == None then
      recover(
        ExpectedTokenError(K.Then, emptySiteAtLastBoundary),
        (e) => Match.Case(p, ErrorTree(e), s.get.extendedTo(lastBoundary)))
    else
      val b = expression()
      Match.Case(p, b, s.get.extendedTo(lastBoundary))

  /** Parses and returns a let expression. */
  private[parsing] def let(): Let =
    val start = lastBoundary
    val bind = binding()
    val body = inBraces(expression)
    Let(bind, body, source.span(start, lastBoundary))

  /** Parses and returns a lambda or parenthesized term-level expression. */
  private def lambdaOrParenthesizedExpression(): Expression =
    val start = lastBoundary
    val snap = snapshot()
    val exp = inParentheses(expression)

    if (peek.exists(K.LBrace.matches)) {
      restore(snap)
      val inputs = valueParameterList()
      val output = take(K.Arrow).map((_) => tpe())
      val body = inBraces(expression)
      Lambda(inputs, output, body, source.span(start, lastBoundary))
    }
    else ParenthesizedExpression(exp, source.span(start, lastBoundary))

  /** Parses and returns an operator. */
  private def operator(): Expression =
    operatorIdentifier() match
      case (Some(o), p) => Identifier(p.text.toString, p)
      case (_, p) => ErrorTree(p)

  /** Parses and returns an operator identifier, along with its source positions.
   *
   *  If the the parsed operator is undefined, a diagnostic is reported and the returned identifier
   *  is `None`. In any case, the returned span represents the positions of the parsed identifier.
   */
  private def operatorIdentifier(): (Option[ast.OperatorIdentifier], SourceSpan) =
    import ast.OperatorIdentifier as O

    @tailrec def loop(start: Int, end: Int): (Option[ast.OperatorIdentifier], SourceSpan) =
      if takeIf((t) => t.isOperatorPartImmediatelyAfter(end)) != None then
        loop(start, lastBoundary)
      else
        val p = source.span(start, end)
        val s = p.text
        val o = if s == "||" then
          Some(O.LogicalOr)
        else if s == "&&" then
          Some(O.LogicalAnd)
        else if s == "<" then
          Some(O.LessThan)
        else if s == "<=" then
          Some(O.LessThanOrEqual)
        else if s == ">" then
          Some(O.GreaterThan)
        else if s == ">=" then
          Some(O.GreaterThanOrEqual)
        else if s == "==" then
          Some(O.Equal)
        else if s == "!=" then
          Some(O.NotEqual)
        else if s == "..." then
          Some(O.ClosedRange)
        else if s == "..<" then
          Some(O.HaflOpenRange)
        else if s == "+" then
          Some(O.Plus)
        else if s == "-" then
          Some(O.Minus)
        else if s == "|" then
          Some(O.BitwiseOr)
        else if s == "^" then
          Some(O.BitwiseXor)
        else if s == "*" then
          Some(O.Star)
        else if s == "/" then
          Some(O.Slash)
        else if s == "%" then
          Some(O.Percent)
        else if s == "&" then
          Some(O.Ampersand)
        else if s == "<<" then
          Some(O.LeftShift)
        else if s == ">>" then
          Some(O.RightShift)
        else if s == "~" then
          Some(O.Tilde)
        else if s == "!" then
          Some(O.Bang)
        else
          report(SyntaxError(s"undefined operator '${s}'", p))
          None
        (o, p)

    val h = expect("operator", (t) => t.kind.isOperatorPart)
    loop(h.site.start, h.site.end)

  /** Parses and returns a type cast operator. */
  private def typecast(): Option[Typecast] =
    peek match
      case Some(Token(K.At, _)) =>
        take(); Some(Typecast.Widen)
      case Some(Token(K.AtQuery, _)) =>
        take(); Some(Typecast.Narrow)
      case Some(Token(K.AtBang, _)) =>
        take(); Some(Typecast.NarrowUnconditionally)
      case _ =>
        None

  // --- Types ----------------------------------------------------------------

  /** Parses and returns a type-level expression. */
  private[parsing] def tpe(): Type =
    val start = lastBoundary
    val types = takeTypes()
    val end = lastBoundary
    val span = SourceSpan(types.head.site.file, start, end)
    if (types.isEmpty) throw FatalError("Expected types defined", emptySiteAtLastBoundary)
    else if (types.length > 1) Sum(types, span)
    else types.head

  /** Retrieves the sum of types*/
  private def takeTypes(x: Boolean = false): List[Type] =
    val s = primaryType()
    takeIf(_.site.text.toString.equals("|")) match {
      case Some(_) => s :: takeTypes(true)
      case None => List(s)
    }

  /** Parses and returns a type-level primary exression. */
  private def primaryType(): Type =
    peek match
      case Some(Token(K.Identifier, s)) =>
        typeIdentifier()
      case Some(Token(K.Label, _)) =>
        recordType()
      case Some(Token(K.LParen, _)) =>
        arrowOrParenthesizedType()
      case _ =>
        recover(ExpectedTree("type expression", emptySiteAtLastBoundary), ErrorTree.apply)

  /** Parses and returns a type identifier. */
  private def typeIdentifier(): TypeIdentifier =
    val s = identifier()
    TypeIdentifier(s.value, s.site)

  /** Parses and returns a list of type arguments. */
  private def typeArguments(): List[Labeled[Type]] =
    inParentheses(() => commaSeparatedList(K.RParen.matches, () => labeled(typeIdentifier)))

  /** Parses and returns a type-level record expressions. */
  private[parsing] def recordType(): RecordType =
    record(recordTypeFields, RecordType.apply)

  /** Parses and returns the fields of a type-level record expression. */
  private def recordTypeFields(): List[Labeled[Type]] =
    parenthesizedLabeledList(typeIdentifier)

  /** Parses and returns a arrow or parenthesized type-level expression. */
  private[parsing] def arrowOrParenthesizedType(): Type =
    val start = lastBoundary
    val t = typeArguments()

    take(K.Arrow) match {
      case Some(_) =>
        Arrow(t, tpe(), source.span(start, lastBoundary))
      case None => ParenthesizedType(t.head.value, source.span(start, lastBoundary))
    }

  // --- Patterns -------------------------------------------------------------

  /** Parses and returns a pattern. */
  private[parsing] def pattern(): Pattern =
    peek match
      case Some(Token(K.Underscore, _)) =>
        wildcard()
      case Some(Token(K.Label, _)) =>
        recordPattern()
      case Some(Token(K.Let, _)) =>
        bindingPattern()
      case _ =>
        valuePattern()

  /** Parses and returns a wildcard pattern. */
  def wildcard(): Wildcard =
    val start = lastBoundary
    if (take(K.Underscore).isEmpty) report(ExpectedTokenError(K.Underscore, emptySiteAtLastBoundary))
    Wildcard(source.span(start, lastBoundary))

  /** Parses and returns a record pattern. */
  private def recordPattern(): RecordPattern =
    record(recordPatternFields, RecordPattern.apply)

  /** Parses and returns the fields of a record pattern. */
  private def recordPatternFields(): List[Labeled[Pattern]] =
    parenthesizedLabeledList(pattern)

  /** Parses and returns a binding pattern. */
  private def bindingPattern(): Binding =
    val start = lastBoundary
    val b = binding(false)
    if (b.initializer.nonEmpty) report(SyntaxError("Binding should not have an initializer!", source.span(start, lastBoundary)))
    b

  /** Parses and returns a value pattern. */
  private def valuePattern(): ValuePattern =
    val start = lastBoundary
    val exp = expression()
    ValuePattern(exp, source.span(start, lastBoundary))

  // --- Common trees ---------------------------------------------------------

  /** Parses and returns an identifier. */
  private def identifier(): Identifier =
    val s = expect(K.Identifier)
    Identifier(s.site.text.toString, s.site)

  // --- Combinators ----------------------------------------------------------

  /** Parses and returns a record.
   *
   *  @param fields A closure parsing the fields of the record.
   *  @param make A closure constructing a record tree from its name, fields, and site.
   */
  private def record[Field <: Labeled[Tree], T <: RecordPrototype[Field]](
      fields: () => List[Field],
      make: (String, List[Field], SourceSpan) => T
  ): T =
    val start = lastBoundary
    val iden = expect(K.Label).site.text.toString
    val fs = if (peek.exists(K.LParen.matches)) fields() else Nil
    make(iden, fs, source.span(start, lastBoundary))

  /** Parses and returns a parenthesized list of labeled value.
   *
   *  See also [[this.labeledList]].
   *
   *  @param value A closure parsing a labeled value.
   */
  private[parsing] def parenthesizedLabeledList[T <: Tree](
      value: () => T
  ): List[Labeled[T]] =
    inParentheses(() => commaSeparatedList(K.RParen.matches, () => labeled(value)))

  /** Parses and returns a value optionally prefixed by a label.
   *
   *  This combinator attempts to parse a label `n` followed by a colon and then applies `value`.
   *  If that succeeds, returned tree is the result of `value` labeled by `n`. If there is no label,
   *  the combinator backtracks, re-applies `value`, and returns its result sans label.
   *
   *  @param value A closure parsing a labeled value.
   */
  private[parsing] def labeled[T <: Tree](
      value: () => T
  ): Labeled[T] =
    val start = lastBoundary
    val snap = snapshot()
    val exp = take()
    val (label, v) = take(K.Colon) match {
      case Some(_) =>
        (Some(exp.map(_.site.text.toString).getOrElse("")), value())
      case None =>
        restore(snap)
        (None, value())
    }
    val end = lastBoundary

    Labeled(label, v, source.span(start, end))

  /** Parses and returns a sequence of `element` separated by commas and delimited on the RHS  by a
   *  token satisfying `isTerminator`.
   */
  private[parsing] def commaSeparatedList[T](isTerminator: Token => Boolean, element: () => T): List[T] =
    @tailrec def loop(partialResult: List[T]): List[T] =
      if peek.map(isTerminator).getOrElse(false) then
        partialResult
      else
        val nextPartialResult = partialResult :+ recovering(K.Comma.matches, element)
        if peek.map(isTerminator).getOrElse(false) then
          nextPartialResult
        else if take(K.Comma) != None then
          loop(nextPartialResult)
        else
          report(ExpectedTokenError(K.Comma, emptySiteAtLastBoundary))
          loop(nextPartialResult)
    loop(List())

  /** Parses and returns `element` surrounded by a pair of parentheses. */
  private[parsing] def inParentheses[T](element: () => T): T =
    delimited(K.LParen, K.RParen, element)

  /** Parses and returns `element` surrounded by a pair of braces. */
  private[parsing] def inBraces[T](element: () => T): T =
    delimited(K.LBrace, K.RBrace, element)

  /** Parses and returns `element` surrounded by angle brackets. */
  private[parsing] def inAngles[T](element: () => T): T =
    delimited(K.LAngle, K.RAngle, element)

  /** Parses and returns `element` surrounded by a `left` and `right`. */
  private[parsing] def delimited[T](left: Token.Kind, right: Token.Kind, element: () => T): T =
    if take(left) == None then
      report(ExpectedTokenError(right, emptySiteAtLastBoundary))
    val contents = recovering(right.matches, element)
    if take(right) == None then
      report(ExpectedTokenError(right, emptySiteAtLastBoundary))
    contents

  /** Returns the result of `element` with `isRecoveryToken` added to the recovery predicates. */
  private def recovering[T](isRecoveryToken: Token => Boolean, element: () => T): T =
    recoveryPredicates += isRecoveryToken
    try
      element()
    finally
      recoveryPredicates.dropRightInPlace(1)

  // --- Utilities ------------------------------------------------------------

  /** Returns `true` iff there isn't any whitespace before the next token in the stream. */
  private def noWhitespaceBeforeNextToken: Boolean =
    peek.map((t) => lastBoundary == t.site.start).getOrElse(false)

  /** Reports a missing identifier and returns "_". */
  def missingName =
    report(ExpectedTokenError(K.Identifier, emptySiteAtLastBoundary))
    "_"

  /** Reports `error`, advances the stream to the next recovery token, and returns the result of
   *  calling `errorTree` on the skipped positions.
   */
  private def recover[T](error: SyntaxError, errorTree: SourceSpan => T): T =
    report(error)
    errorTree(discardUntilRecovery())

  /** Advances the stream to the next recovery token and returns the skipped positions. */
  private def discardUntilRecovery(): SourceSpan =
    @tailrec def loop(s: Int): SourceSpan =
      if !peek.isDefined || Reverse(recoveryPredicates).exists((p) => p(peek.get)) then
        source.span(s, lastBoundary)
      else
        take()
        loop(s)
    loop(lastBoundary)

  /** Consumes and returns the next token in the stream iff it has kind `k` or throw an exception
    * otherwise,
    */
  private def expect(construct: String, predicate: (Token) => Boolean): Token =
    takeIf(predicate) match
      case Some(next) => next
      case _ => throw FatalError(s"expected ${construct}", emptySiteAtLastBoundary)

  /** Consumes and returns the next token in the stream iff it has kind `k` or throw an exception
    * otherwise,
    */
  private def expect(k: Token.Kind): Token =
    take(k) match
      case Some(next) => next
      case _ => throw FatalError(s"expected ${k}", emptySiteAtLastBoundary)

  /** Returns the next token in the stream without consuming it. */
  private def peek: Option[Token] =
    if lookahead == None then
      lookahead = tokens.next()
    lookahead

  /** Consumes the next token in the stream iff it has kind `k` and returns the result of `action`
   *  applied on that token. */
  private def taking[T](k: Token.Kind, action: Token => T): Option[T] =
    take(k).map(action)

  /** Consumes and returns the next token in the stream. */
  private def take(): Option[Token] =
    peek.map({ (next) =>
      lastBoundary = next.site.end
      lookahead = None
      next
    })

  /** Consumes and returns the next token in the stream iff it has kind `k`. */
  private def take(k: Token.Kind): Option[Token] =
    takeIf(k.matches)

  /** Consumes and returns the next character in the stream iff it satisfies `predicate`. */
  private def takeIf(predicate: Token => Boolean): Option[Token] =
    if peek.map(predicate).getOrElse(false) then take() else None

  /** Returns an empty range at the position of the last consumed token. */
  private def emptySiteAtLastBoundary: SourceSpan =
    source.span(lastBoundary, lastBoundary)

  /** Reports the given diagnostic. */
  private def report(d: SyntaxError): Unit =
    errors += d

  /** Returns a backup of this instance's state. */
  private[parsing] def snapshot(): Parser.Snapshot =
    Parser.Snapshot(
      tokens.copy(), lastBoundary, lookahead, errors.length, recoveryPredicates.length)

  /** Restores this instance to state `s`. */
  private[parsing] def restore(s: Parser.Snapshot): Unit =
    tokens = s.tokens
    lastBoundary = s.lastBoundary
    lookahead = s.lookahead
    errors.dropRightInPlace(errors.length - s.errorCount)
    recoveryPredicates.dropRightInPlace(recoveryPredicates.length - s.recoveryPredicateCount)

end Parser

object Parser:

  /** The information necessary to restore the state of a parser instance. */
  private[parsing] final case class Snapshot(
      tokens: Lexer,
      lastBoundary: Int,
      lookahead: Option[Token],
      errorCount: Int,
      recoveryPredicateCount: Int)

end Parser

extension (self: Token.Kind) def | (other: Token.Kind): (Token) => Boolean =
  (t) => (t.kind == self) || (t.kind == other)

extension (self: Token => Boolean) def | (other: Token.Kind): (Token) => Boolean =
  (t) => self(t) || (t.kind == other)
