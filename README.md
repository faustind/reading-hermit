# Paper Reading Report

## Gunma University, Software Science Laboratory


This repository is a report of my reading the paper

> A. Farmer, N. Sculthorpe, and A. Gill, “Reasoning with the HERMIT: Tool support 
> for equational reasoning on GHC Core programs,” in Proceedings of the 8th ACM 
> SIGPLAN Symposium on Haskell, Haskell 2015, (New York, NY, USA), pp. 23–34, ACM, 2015.

## Equational Reasoning

Let's set the stage with some examples from [1]. We are all familiar with the 
algebraic laws

```text
xy = yx {commutativity}
x + (y + z) = (x + y) + z {associativity}
x (y + z) = xy + xz {left distributivity}
(x + y) z = xz + yz {right distributivity}
```

We can use them to prove the equality `(x + a) (x + b) = x^2 + (a + b)x + ab` in the
following manner:

```text
 (x + a) (x + b)
=   {left distributivityi}
 (x + a)x + (x + a)b
=   {right distributivity}
 x^2 + ax + xb + ab
=   {commutativity}
 x^2 + ax + bx + ab (1)
=   {right distributivity}
 x^2 + (a + b)x + ab (2)
```

From a computational perspective the expression (1) is less efficient than (2).
This shows how equational resoning may be used to improve the efficiency of 
some computation.

## Reasoning about Haskell Programs

Because Haskell programs are similar to mathematical functions, it is possible
apply this form of equational resoning to Haskell programs. Hakell's function definitions can then be
viewed as __laws__ or __properties__ saying that the left-hand side may be replaced by
the right-hand side. For example, from the definition

```haskell
double :: Int -> Int
double x = x + x
```

we know that we may substitute `double x` for `x + x` and vice-versa in a program 
containing the definition. As another example, let's see how we can use the definition 

```haskell
reverse :: [a] -> [a]
reverse []     = []
reverse (x:xs) = reverse xs ++ [x]
```

to show the (obvious) equivalence `reverse [x] = [x]`. The proof goes as follow

```text
 reverse [x]
=   {list notation}
 reverse (x:[])
=   {apply reverse}
 reverse [] ++ [x]
=   {apply reverse}
 [] ++ [x]
=   {apply ++}
 [x]
```

Note that the result is more efficient because it does not require a function application.
We can instruct GHC to substitute `[x]` for `reverse [x]` during its optimization passes
using the rewrite rules pragma as demonstrated in [2].

Let's apply what we know to proving `forall f g. map f . map g = map (f . g)`.
Recall the definition of `map`

```haskell
map :: (a -> b) -> [a] -> [b]
map f []     = []
map f (a:as) = f a : map f as
```

Both side of the equality can be modified to obtain the equivalent goal

```text
map f (map g xs) = map (λ x -> f (g x)) xs
```

With the argument made explicit, we can use induction on its structure. 
For the base case, by definition of `map`

```text
map (λ x -> f (g x)) [] = []
```

Also

```text
 map f (map g [])
=   {apply map}
 map f []
=   {apply map}
 []
 ```

Hence the target proposition holds for empty lists. Now, for `xs = (a:as)`
we have the following transformations

```text
 map f (map g (a:as))
=   {apply map}
map f (g a : map g as)
=   {apply map}
f (g a) : map f (map g as)
=   {induction hypothesis}
(λ x -> f (g x)) a : map (λ x -> f (g x)) as
=   {apply map}
map (λ x -> f (g x)) (a:as)
```

And this conclude the proof that

```text
forall f g. map f . map g = map (f . g)
```

## The main Idea

Now, imagine that we have a program relying on the equivalence we have just proved ; and some 
months later we update our definition of `map`. Since the proof of the equivalence rely on
the definiion of `map`, we would need to redo it to make sure that we are not lying to say the compiler.
For such small examples, it is easily done. However, consider what the task could
look like for the proofs that all type class laws holds for all the instances defined in a
real world project.

**I think the main idea in the paper is that we should automate the proofs once we know the steps involved.**
The suggested approach is to

1. Prove the properties using the HERMIT repl
2. Export the commands sequence in HERMIT scripts
3. Configure the build pipeline to automatically check the proof at compile time

Instead of recouring to languages and tools external to Haskell such as Agda or Coq

> HERMIT is a Haskell-specific toolkit designed to support equational reasoning
> and user-guided program transformation, and to do so as part of the GHC 
> compilation pipeline.

The paper presents several contributions, notably:

1. HERMIT can now be used to check preconditions
2. HERMIT can now be used to reason about auxiliary properties of programs being transformed
3. HERMIT now provides built-in structural induction over algebraic data types.

> The initial HERMIT implementation only supported equational reasoning that was 
> transformational in nature. 
> [...] Some of the transformation steps used were only valid in certain contexts, and HERMIT
> had no facility for checking the necessary preconditions. Thus these preconditions had to 
> be verified by hand. Furthermore, it was not possible to state and reason about auxiliary
> properties of the program being transformed, or to use inductive techniques to verify their
> correctness.

Let's use HERMIT to interactively check our proof that

```text
forall f g. map f . map g = map (f . g)
```

Assuming you have stack installed, clone this repository, move to the created directory and
run 

```bash
$ stack build
$ stack exec hermit src/Examples.hs
```

The expected output is 

```haskell
[starting HERMIT v1.0.0.0 on src/Examples.hs]
% ghc src/Examples.hs -fforce-recomp -O2 -dcore-lint ...
[1 of 1] Compiling Examples         ( src/Examples.hs, src/Examples.o ) 
.
.
.
======================= Welcome to HERMIT ================================
HERMIT is a toolkit for the interactive transformation of GHC Core language
programs...
.
.
.
=========================================================================

module Example where
    map :: ∀ a b . (a → b) → [a] → [b]
hermit<0>
```

The last line is an invitation to enter HERMIT commands. 
Entering the uncommented lines to the prompt will lead to the verification of the proof.
This the example of interactive proof checking from the paper.

```haskell
set-pp-type Omit

-- module main:MapFusion where map :: forall a b . (a -> b) -> [a] -> [b]

binding-of 'map

-- map = \ f ds ->
--   case ds of wild
--     [] -> []
--     (:) a as -> (:) (f a) (map f as)

top

-- module main:MapFusion where map :: forall a b . (a -> b) -> [a] -> [b]

rule-to-lemma map-fusion
prove-lemma map-fusion

-- Goal:
-- forall f g. (.) (map f) (map g) = map ((.) f g)

extensionality 'xs

-- Goal:
-- forall f g xs. (.) (map f) (map g) xs = map ((.) f g) xs

lhs (unfold '.)

-- Goal:
-- forall f g xs. map f (map g xs) = map ((.) f g) xs

induction 'xs

-- Goal:
-- forall f g.
-- (map f (map g undefined) = map ((.) f g) undefined)
-- ^
-- ((map f (map g []) = map ((.) f g) [])
--  ^
--  (forall a b. (map f (map g b) = map ((.) f g) b) => (map f (map g ((:) a b)) = map ((.) f g) ((:) a b))))

any-bu ((unfold 'map) >>> (undefined-case <+ case-reduce))

-- Goal:
-- forall f g.
-- (undefined = undefined)
-- ^
-- (([] = [])
--  ^
--  (forall a b.
--   (map f (map g b) = map ((.) f g) b)
--   =>
--   ((:) (f (g a)) (map f (map g b)) = (:) ((.) f g a) (map ((.) f g) b))))

simplify-lemma

-- Goal:
-- forall f g a b.
-- (map f (map g b) = map ((.) f g) b)
-- =>
-- ((:) (f (g a)) (map f (map g b)) = (:) ((.) f g a) (map ((.) f g) b))

forall-body

-- Goal:
-- (map f (map g b) = map ((.) f g) b)
-- =>
-- ((:) (f (g a)) (map f (map g b)) = (:) ((.) f g a) (map ((.) f g) b))

consequent

-- Notice when we move past the antecedent, it comes into scope!

-- Assumed lemmas:
-- ind-hyp-0 (Built In)
--   map f (map g b) = map ((.) f g) b
-- Goal:
-- (:) (f (g a)) (map f (map g b)) = (:) ((.) f g a) (map ((.) f g) b)

one-td (lemma-forward ind-hyp-0)

-- Assumed lemmas:
-- ind-hyp-0 (Built In)
--   map f (map g b) = map ((.) f g) b
-- Goal:
-- (:) (f (g a)) (map ((.) f g) b) = (:) ((.) f g a) (map ((.) f g) b)

simplify

-- Assumed lemmas:
-- ind-hyp-0 (Built In)
--   map f (map g b) = map ((.) f g) b
-- Goal:
-- (:) (f (g a)) (map ((.) f g) b) = (:) (f (g a)) (map ((.) f g) b)

end-case -- proven map-fusion

-- module main:MapFusion where map :: forall a b . (a -> b) -> [a] -> [b]

```

As any good researcher, the authors raise some issues of their current implentation
and present some possible considerations for furture work. For example on the 
introduced structural induction principle they say

> This form of structural induction is somewhat limited in that it only allows
> the induction hypothesis to be applied to a variable one constructor deep. We 
> are currently in the process of implementing a more general induction 
> principle that will allow the inductive hypothesis to be applied to a variable 
> n constructors deep.

Also

> […] Some of the transformations provided by HERMIT only offer partial correctness.
> […] In the next version we intend to allow the user the option of disabling the 
> set of partially correct transfomations, and of enforcing that any preconditions 
> are satisfied before a transformation can be used.

Finally

> A substantial avenue for future work is to create a mechanical connection
> between HERMIT’s primitive transformations and a semantic model, so that 
> they can be formally verified.

There is a useful technique in equational reasoning that _is not supported_ 
by HERMIT at the time of the publication. To illustrate, consider this other example
also from [1]: the computation of an efficient version of `reverse`. To avoid the 
quadradic time induced by the use of `++` in the previous definition Graham Hutton
specify a new function `reverse'` such that

```haskell
reverse' xs ys = reverse xs ++ ys
```

And insted of giving a defintion of `reverse'` and proving that it satisfies the 
specification above, he _derives the definition from the specification_ by induction
on `xs`.

Base case:

```text
 reverse' [] ys
=   {specification of reverse'}
 reverse [] ++ ys
=   {apply revere}
 [] ++ ys
=   {apply ++}
 ys
```

Inductive case:

```text
reverse' (x:xs) ys
= {specification of reverse'}
reverse (x:xs) ++ ys
= {apply reverse}
(reverse xs ++ [x]) ++ ys
= {associativity of ++}
reverse xs ++ ([x] ++ ys)
= {induction hypothesis}
reverse' xs ([x] ++ ys)
= {apply ++}
reverse' xs (x : ys)
```

The conclusion is

```haskell
reverse' :: [a] -> [a] -> [a]
reverse' [] ys     = ys
reverse' (x:xs) ys = reverse' xs (x : ys)
```

Finally a nicer version of `reverse` is defined

```haskell
reverse :: [a] -> [a]
reverse xs = reverse' xs []
```

The derivations of programs in such a backward manner although not supported can
still be verified by using the resulting definition as a goal in a verification
of the specification.

## References

1. Programming in Haskell, 2nd Ed, Graham Hutton
2. Playing by the Rules: Rewriting as a practical optimisation technique in GHC, Peyton J. et al

