-- Prove2me | solution 1 for ThreeSum.LightCyclic.correlation_meets
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T16:34:50.231457+00:00
-- url     : https://prove2.me/submissions/6f07a6bb-7f77-4c56-b700-367d34c2479c

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorems.Thm_ThreeSum_CyclicFold_cyclic_correlation
import Theorems.Thm_ThreeSum_Karatsuba_product_coeff_bound
import Theorems.Thm_ThreeSum_LightArray_linear_bounded_meets
import Theorems.Thm_ThreeSum_LightKaratsuba_meets


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.CyclicFold
end ThreeSum.CyclicFold
namespace ThreeSum.Karatsuba
end ThreeSum.Karatsuba
namespace ThreeSum.LightKaratsuba
end ThreeSum.LightKaratsuba

section


/-!
# Dense integer Karatsuba multiplication

This file implements a dense, low-coefficient-first list algorithm. Its
correctness theorem is an equality of integer polynomials. The instrumented
work model counts list traversal and scalar arithmetic primitives; it is a
separate obligation to compile this implementation to `Light` and prove the
benchmark's word-RAM step and word-size bounds.
-/

namespace ThreeSum.Karatsuba

open Polynomial








































































/-- Splitting at a coefficient boundary is exact, also for padded short lists. -/
theorem asPolynomial_split (n : ℕ) (as : List ℤ) :
    asPolynomial as = asPolynomial (as.take n) + X ^ n * asPolynomial (as.drop n) := by
  induction n generalizing as with
  | zero => simp [asPolynomial]
  | succ n ih =>
    cases as with
    | nil => simp [asPolynomial]
    | cons a as =>
      simp only [List.take_succ_cons, List.drop_succ_cons, asPolynomial, pow_succ]
      rw [ih as]
      ring













































































/-! ## Explicit traversal/arithmetic work model

The following charges reflect the operations in the executable list code:
two units per matched coefficient of `plus`; two per mapped coefficient of
`negate`; two per generated/concatenated zero of `shift`; and the two scans
used by `take` and `drop`. The fixed per-call charges include list tests.
They are a conventional unit-cost list/arithmetic model, **not** a theorem
about the benchmark machine or Lean's runtime system.

The recursive charge below uses the actual intermediate list sizes. The
uniform three-subcall recurrence is proved from those sizes; it is not an
assumption that the desired multiplication bound already holds.
-/




















































































end ThreeSum.Karatsuba

end

section


/-! # Coefficient and intermediate-value bounds for the array realization -/

namespace ThreeSum.Karatsuba

open Polynomial
open scoped BigOperators

@[simp] theorem asPolynomial_coeff (as : List ℤ) (j : ℕ) :
    (asPolynomial as).coeff j = as.getD j 0 := by
  induction as generalizing j with
  | nil => simp [asPolynomial]
  | cons a as ih =>
    cases j with
    | zero => simp [asPolynomial]
    | succ j =>
      rw [asPolynomial, Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_X_mul, ih]
      simp
































































































end ThreeSum.Karatsuba

end

section


/-!
# Folding a dense polynomial product into a cyclic convolution

The product of two vectors of length at most `p` has only two possible
contributions to an output residue `r < p`: coefficients `r` and `r+p`.
The double sum below specifies the answer; the implementation obtains it
by one fast product and a linear pass over the output coefficients.
-/

namespace ThreeSum.CyclicFold

open Finset Polynomial Karatsuba
open scoped BigOperators

theorem asPolynomial_sum (as : List ℤ) (p : ℕ) (ha : as.length ≤ p) :
    asPolynomial as = ∑ i ∈ Finset.range p, monomial i (as.getD i 0) := by
  apply Polynomial.ext
  intro k
  simp only [asPolynomial_coeff, finsetSum_coeff, coeff_monomial]
  by_cases hk : k < p
  · simp [hk, eq_comm]
  · rw [List.getD_eq_default _ _ (by omega)]
    simp [hk, eq_comm]

theorem product_coeff_double (as bs : List ℤ) (p : ℕ)
    (ha : as.length ≤ p) (hb : bs.length ≤ p) (r : ℕ) :
    (asPolynomial as * asPolynomial bs).coeff r =
      ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range p,
        if i + j = r then as.getD i 0 * bs.getD j 0 else 0 := by
  rw [asPolynomial_sum as p ha, asPolynomial_sum bs p hb]
  simp only [sum_mul_sum, finsetSum_coeff, monomial_mul_monomial, coeff_monomial]

theorem mod_indicator {p i j r : ℕ} (hi : i < p) (hj : j < p) (hr : r < p)
    (w : ℤ) :
    (if i + j = r then w else 0) + (if i + j = r + p then w else 0) =
      if (i + j) % p = r then w else 0 := by
  by_cases hsum : i + j < p
  · rw [Nat.mod_eq_of_lt hsum]
    split_ifs <;> omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    split_ifs <;> omega





theorem fold_product (as bs : List ℤ) (p r : ℕ)
    (ha : as.length ≤ p) (hb : bs.length ≤ p) (hr : r < p) :
    (asPolynomial as * asPolynomial bs).coeff r +
      (asPolynomial as * asPolynomial bs).coeff (r + p) = cyclic p as bs r := by
  rw [product_coeff_double as bs p ha hb, product_coeff_double as bs p ha hb]
  rw [← sum_add_distrib]
  unfold cyclic
  apply sum_congr rfl
  intro i hi
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro j hj
  exact mod_indicator (mem_range.mp hi) (mem_range.mp hj) hr _




theorem vector_length (p : ℕ) (f : ZMod p → ℕ) : (vector p f).length = p := by
  simp [vector]







































































theorem padTo_length (n : ℕ) (as : List ℤ) (ha : as.length ≤ n) :
    (padTo n as).length = n := by
  simp [padTo, Nat.add_sub_of_le ha]

@[simp] theorem asPolynomial_replicate_zero (n : ℕ) :
    asPolynomial (List.replicate n 0) = 0 := by
  induction n with
  | zero => simp [asPolynomial]
  | succ n ih => simp [List.replicate_succ, asPolynomial, ih]

theorem asPolynomial_padTo (n : ℕ) (as : List ℤ) :
    asPolynomial (padTo n as) = asPolynomial as := by
  rw [asPolynomial_split as.length]
  simp [padTo]

theorem coeffBound_padTo {as : List ℤ} {U : ℤ} (h : CoeffBound as U) (n : ℕ) :
    CoeffBound (padTo n as) U := by
  intro j
  rw [← asPolynomial_coeff, asPolynomial_padTo, asPolynomial_coeff]
  exact h j











end ThreeSum.CyclicFold

end

section


/-!
# Proof rules for the light language

Ends lim P d s σ T Q says: the statement s, started in σ, ends within T steps in a state that
satisfies Q.  There is one rule for each construct; a rule turns a goal about a statement into goals
about its parts, so a proof follows the text of the program from top to bottom.  Recursion needs no
rule: a statement about a recursive procedure is proved by induction (in Lean) on a measure, and the
rule for calls unfolds the body.

There are three rules for loops: with an invariant indexed by the number of the round and a cost for
each round (Ends.while), the same with one cost for all rounds (Ends.whileConst), and, for a loop
whose number of rounds depends on the data, with a quantity that every round decreases
(Ends.whileVariant).

The file also has the basic facts about runs (a run stays a run when procedures are appended to the
program), notation for writing programs, the simplification set
`light_norm`, and the standing assumptions `Std` about the limits.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## Runs -/



































/-! ## The rules -/






/-- More time and a weaker conclusion. -/
theorem Ends.mono {s σ T T' Q Q'} (h : Ends lim P d s σ T Q) (hT : T ≤ T')
    (hQ : ∀ σ', Q σ' → Q' σ') : Ends lim P d s σ T' Q' := by
  obtain ⟨σ', c, he, hc, hq⟩ := h
  exact ⟨σ', c, he, hc.trans hT, hQ _ hq⟩







theorem Ends.skip {σ T} {Q : State → Prop} (h : Q σ) : Ends lim P d .skip σ T Q :=
  ⟨σ, 0, .skip, Nat.zero_le _, h⟩











theorem Ends.seq {σ T s₁ s₂} {Q : State → Prop} (T₁ T₂ : ℕ)
    (h : Ends lim P d s₁ σ T₁ fun σ' => Ends lim P d s₂ σ' T₂ Q) (hT : T₁ + T₂ ≤ T) :
    Ends lim P d (.seq s₁ s₂) σ T Q := by
  obtain ⟨σ', c₁, he₁, hc₁, σ'', c₂, he₂, hc₂, hq⟩ := h
  exact ⟨σ'', _, .seq he₁ he₂, by omega, hq⟩

























































































/-- Calls: verify the body from the frame made of the arguments. -/
theorem Ends.call {σ T p args x body} {Q : State → Prop} (T' : ℕ) (ha : ∀ e ∈ args, e.Safe lim σ)
    (hp : P[p]? = some body) (hd : d < lim.depth)
    (h : Ends lim P (d + 1) body ⟨frame (args.map (·.val σ)), σ.mem⟩ T'
      fun σ' => Q ⟨Function.update σ.loc x (σ'.loc 0), σ'.mem⟩)
    (hT : (args.map Expr.cost).sum + 2 + T' ≤ T) : Ends lim P d (.call p args x) σ T Q := by
  obtain ⟨σ', k, he, hk, hq⟩ := h
  exact ⟨_, _, .call ha hp hd he, by omega, hq⟩

/-! ## Notation for writing programs

Not trusted: a theorem about a program does not depend on how the program was typed in. -/




























/-! ## Simplification -/

attribute [simp] Expr.val Expr.cost Expr.Safe Op.eval Cond.Holds Cond.cost Cond.Safe frame
















/-! ## The limits -/
























end Light

end
end

section


/-!
# Derived rules: time that is not typed, blocks, counting loops

The rules of this file spare the typing of step counts.  Ends.next gives the first statement its
time and the rest of the program what is left; Ends.setThen, Ends.storeThen and Ends.iteThen do the
same for one assignment, store or branch, and Ends.setLast, Ends.storeLast and Ends.iteLast treat
the last statement of a program.  `Ends.pieceThen` and `Ends.pieceLast` are the two forms for a
piece of the program that has a lemma of its own.  In every rule the main premises come first, then
the side conditions, and last the comparison of times.  The comparison has the default proof
`light_time`, safety conditions have the default proof `light_side`.

A block is a statement without loops and calls.  s.Runs lim σ R says that the block s runs safely
from σ and ends in a state that satisfies R; Ends.block turns this into a fact about time, with the
cost computed. Ends.whileBlock is the rule for a loop whose body is a block.

Stmt.for i hi body is the loop "for i = 0, …, hi - 1 do body".  The rule Ends.for owns the counter:
the safety of the test and of the increment and the number of steps of the loop are settled here,
once. Ends.forMem is the common case in which the body changes no local variable, so that the
invariant speaks about the memory only.  The three parts of every loop rule are called start, round
and done.  A loop rule is told a bound b on the steps of a round; for a round that is a block with
a name, say xRound, this is xRound.blockCost.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## Blocks -/




































/-! ## The default proofs -/



































/-! ## Rules for blocks -/















































/-! ## Sequencing: what is left of the time goes to the rest of the program -/

/-- The first statement gets T₁ steps, the rest of the program what is left of T. -/
theorem Ends.next {σ : State} {T : ℕ} {s₁ s₂ : Stmt} {Q : State → Prop} (T₁ : ℕ)
    (h : Ends lim P d s₁ σ T₁ fun σ' => Ends lim P d s₂ σ' (T - T₁) Q)
    (hT : T₁ ≤ T := by first
                           |
                             ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                   List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                               (first
                                 | omega
                                 | ((ring_nf); (omega))))
                           | omega
                           |
                             (simp [] <;>
                                 first
                                 | omega
                                 | ((ring_nf); (omega)))) : Ends lim P d ((Light.Stmt.seq s₁ s₂)) σ T Q :=
  Ends.seq T₁ (T - T₁) h (by omega)

/-- Brackets do not matter: a piece of several statements, followed by the rest of the program, is
run statement by statement. -/
theorem Ends.seqAssoc {σ : State} {T : ℕ} {s₁ s₂ s₃ : Stmt} {Q : State → Prop}
    (h : Ends lim P d ((Light.Stmt.seq s₁ (Light.Stmt.seq s₂ s₃))) σ T Q) : Ends lim P d ((Light.Stmt.seq (Light.Stmt.seq s₁ s₂) s₃)) σ T Q := by
  obtain ⟨σ', _, he, hc, hq⟩ := h
  cases he with
  | seq he₁ he₂₃ =>
    cases he₂₃ with
    | seq he₂ he₃ => exact ⟨σ', _, .seq (.seq he₁ he₂) he₃, by omega, hq⟩

/-- A `skip` before the rest of the program takes no step. -/
theorem Ends.skipThen {σ : State} {T : ℕ} {s : Stmt} {Q : State → Prop} (h : Ends lim P d s σ T Q) :
    Ends lim P d ((Light.Stmt.seq .skip s)) σ T Q :=
  Ends.seq 0 T (Ends.skip h) (by omega)

/-- A `skip` may be put behind a statement. -/
theorem Ends.skipLast {σ : State} {T : ℕ} {s : Stmt} {Q : State → Prop}
    (h : Ends lim P d ((Light.Stmt.seq s .skip)) σ T Q) : Ends lim P d s σ T Q := by
  obtain ⟨σ', _, he, hc, hq⟩ := h
  cases he with
  | seq he₁ he₂ =>
    cases he₂
    exact ⟨σ', _, he₁, by omega, hq⟩

/-- A program that is defined as a sequence may be treated as the sequence. -/
theorem Ends.seqSelf {σ : State} {T : ℕ} {s₁ s₂ : Stmt} {Q : State → Prop}
    (h : Ends lim P d ((Light.Stmt.seq s₁ s₂)) σ T Q) : Ends lim P d ((Light.Stmt.seq s₁ s₂)) σ T Q :=
  h












































































/-! ## Loops whose body is a block -/














/-! ## Counting loops -/











































































end Light

end
end

section


/-!
# Local variables as a list

In the proof of a procedure body the state is written out as ⟨frame [a, b, …], μ⟩: the list
holds the local variables 0, 1, …, and all further ones are 0.  An assignment to local x replaces
entry x of the list (setLocal).  The rules of this file treat one statement each.  They are told the
value that is assigned or stored, and they ask for one fact about each expression: that its
evaluation stays within the limits and gives this value (Expr.Gives).  This fact and the comparison
of the costs are proved by default from the hypotheses in the context.  Ends.forFrame and
Ends.forShape are the rules for counting loops in this form.  In the names of the rules, To says
that the state is ⟨frame l, μ⟩.

Locals by name, and locals whose values do not matter:

* `setLocals l [(x, a), (y, b), …]` is the list `l` after the assignments `x := a`, `y := b`, ….
  With the names of the locals for `x`, `y`, … it describes the locals of a procedure by name:
  `setLocals [] [(Size, n), (Bound, U), …]`.
* `updateLocals loc [(x, a), (y, b), …]` is the same for locals that are not given as a list.  A
  lemma about a piece of text that several procedures share is stated for arbitrary locals `loc`.
* `refreshLocals l loc xs` is the list `l` with the entries `xs` read from `loc`.
* `LocalsBut xs l loc` says that `loc` agrees with `frame l` except perhaps at the locals `xs`.  In
  an invariant, `xs` are the scratch variables.  `Ends.asFrame` goes from such locals to a list, and
  `LocalsBut.of_eq` comes back.
* `Ends.pieceTo` and `Ends.pieceToThen` use a lemma about a piece of text that assigns only the
  locals `xs`: afterwards the locals are `refreshLocals l loc' xs`, where `loc'` are the locals of
  which the lemma speaks.  The lemma need not mention the locals that the piece does not assign.
* `Ends.forScratch` is the rule for a counting loop whose body may change the scratch variables
  `xs`: the round says nothing about the locals.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## The list of the locals -/









/-- Reading a local after an assignment. -/
theorem frame_setLocal : ∀ (l : List ℤ) (x : ℕ) (z : ℤ) (y : ℕ),
    frame (setLocal l x z) y = if y = x then z else frame l y
  | [], 0, z, 0 => by simp
  | [], 0, z, y + 1 => by simp
  | [], x + 1, z, 0 => by simp
  | [], x + 1, z, y + 1 => by simpa using frame_setLocal [] x z y
  | a :: l, 0, z, 0 => by simp
  | a :: l, 0, z, y + 1 => by simp
  | a :: l, x + 1, z, 0 => by simp
  | a :: l, x + 1, z, y + 1 => by simpa using frame_setLocal l x z y

/-- An assignment to a local, in terms of the list. -/
theorem update_frame_setLocal (l : List ℤ) (x : ℕ) (z : ℤ) :
    Function.update (frame l) x z = frame (setLocal l x z) := by
  funext y
  rw [frame_setLocal, Function.update_apply]











/-! ## The value of an expression -/





/-! ## One statement -/

section rules

variable {l : List ℤ} {μ : ℕ → ℤ} {T : ℕ} {Q : State → Prop}


















































































































end rules

/-! ## Locals by name, and locals whose values do not matter -/




































































section
variable {xs : List ℕ} {l l' : List ℤ} {loc μ : ℕ → ℤ}

























/-! ## A piece of program text with a lemma of its own -/

variable {T T₁ : ℕ} {s s₁ s₂ : Stmt} {Q R : State → Prop}































/-! ## Counting loops with scratch variables -/













































end

end Light

end
end

section


/-!
# Calls

Meets lim P p d vals μ T R is the specification of a procedure: procedure number p of the program P,
run at depth d on the arguments vals in the memory μ, ends within T steps with a result and a memory
that satisfy R. A routine is proved to meet such a specification (Meets.of_body), and a caller uses
the specification only, so that the proof of a caller does not depend on the body of a callee.

The specification of a routine x, as its callers assume it, has the form
`∀ (data) μ, hypotheses → ∀ d, d + k ≤ lim.depth → Meets lim P p d vals μ T R`.  Here k is the
number of levels of calls that x needs below itself, and d, the depth at which the body of x runs,
comes last.

There is one rule for calls, in four forms.  It is told the fact about the callee, from which it
reads the values of the arguments, the time and what holds afterwards, and it asks for what follows
the call.  Three side goals have default proofs: the arguments are safe and have these values, one
more level of calls is allowed, and the time suffices.  Ends.callTo and Ends.callToThen are the rule
for a state ⟨frame l, μ⟩; Ends.callLast and Ends.callThen are the same for local variables that are
not given as a list.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## Specifications of procedures -/







section
variable {p : ℕ} {vals : List ℤ} {μ : ℕ → ℤ} {T T' : ℕ} {R R' : ℤ → (ℕ → ℤ) → Prop}

/-- From a theorem about a body to the specification. -/
theorem Meets.of_body {args : List ℤ} {Q : ℤ → (ℕ → ℤ) → Prop} {body : Stmt}
    (hp : P[p]? = some body)
    (h : Ends lim P d body ⟨frame args, μ⟩ T fun σ' => Q (σ'.loc 0) σ'.mem) :
    Meets lim P p d args μ T Q :=
  ⟨body, hp, h⟩

/-- More time and a weaker conclusion. -/
theorem Meets.mono (h : Meets lim P p d vals μ T R) (hT : T ≤ T') (hR : ∀ r μ', R r μ' → R' r μ') :
    Meets lim P p d vals μ T' R' := by
  obtain ⟨body, hp, he⟩ := h
  exact ⟨body, hp, he.mono hT fun _ => hR _ _⟩

















end

/-! ## The rule for calls -/

section
variable {loc μ : ℕ → ℤ} {l : List ℤ} {T T' p x : ℕ} {args : List Expr} {vals : List ℤ}
  {R : ℤ → (ℕ → ℤ) → Prop} {Q : State → Prop} {s : Stmt}

/-- `x := p(args)`, where the arguments give vals.  The procedure runs at depth d + 1. -/
theorem Ends.callLast (hp : Meets lim P p (d + 1) vals μ T' R)
    (h : ∀ r μ', R r μ' → Q ⟨Function.update loc x r, μ'⟩)
    (ha : (∀ e ∈ args, e.Safe lim ⟨loc, μ⟩) ∧ args.map (·.val ⟨loc, μ⟩) = vals := by (((try have := Light.Std.space_le (by assumption)));
                                                                                                        ((try have := Light.Std.const_le (by assumption)));
                                                                                                        (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
    (hd : d < lim.depth := by omega)
    (hT : (args.map Expr.cost).sum + 2 + T' ≤ T := by first
                                                        |
                                                          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                                                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                                            (first
                                                              | omega
                                                              | ((ring_nf); (omega))))
                                                        | omega
                                                        |
                                                          (simp [] <;>
                                                              first
                                                              | omega
                                                              | ((ring_nf); (omega)))) :
    Ends lim P d (.call p args x) ⟨loc, μ⟩ T Q := by
  obtain ⟨body, hb, he⟩ := hp
  obtain ⟨hs, rfl⟩ := ha
  exact Ends.call T' hs hb hd (he.mono le_rfl fun _ hR => h _ _ hR) hT











/-- `x := p(args)`, with the local variables as a list.  The procedure runs at depth d + 1. -/
theorem Ends.callTo (hp : Meets lim P p (d + 1) vals μ T' R)
    (h : ∀ r μ', R r μ' → Q ⟨frame (setLocal l x r), μ'⟩)
    (ha : (∀ e ∈ args, e.Safe lim ⟨frame l, μ⟩) ∧ args.map (·.val ⟨frame l, μ⟩) = vals := by
      (((try have := Light.Std.space_le (by assumption)));
        ((try have := Light.Std.const_le (by assumption)));
        (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
    (hd : d < lim.depth := by omega)
    (hT : (args.map Expr.cost).sum + 2 + T' ≤ T := by first
                                                        |
                                                          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                                                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                                            (first
                                                              | omega
                                                              | ((ring_nf); (omega))))
                                                        | omega
                                                        |
                                                          (simp [] <;>
                                                              first
                                                              | omega
                                                              | ((ring_nf); (omega)))) :
    Ends lim P d (.call p args x) ⟨frame l, μ⟩ T Q :=
  Ends.callLast hp (fun r μ' hR => update_frame_setLocal l x r ▸ h r μ' hR) ha hd hT

/-- `x := p(args) ; s`, with the local variables as a list.  The procedure runs at depth d + 1. -/
theorem Ends.callToThen (hp : Meets lim P p (d + 1) vals μ T' R)
    (h : ∀ r μ', R r μ' → Ends lim P d s ⟨frame (setLocal l x r), μ'⟩
      (T - ((args.map Expr.cost).sum + 2 + T')) Q)
    (ha : (∀ e ∈ args, e.Safe lim ⟨frame l, μ⟩) ∧ args.map (·.val ⟨frame l, μ⟩) = vals := by
      (((try have := Light.Std.space_le (by assumption)));
        ((try have := Light.Std.const_le (by assumption)));
        (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
    (hd : d < lim.depth := by omega)
    (hT : (args.map Expr.cost).sum + 2 + T' ≤ T := by first
                                                        |
                                                          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                                                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                                            (first
                                                              | omega
                                                              | ((ring_nf); (omega))))
                                                        | omega
                                                        |
                                                          (simp [] <;>
                                                              first
                                                              | omega
                                                              | ((ring_nf); (omega)))) :
    Ends lim P d ((Light.Stmt.seq (.call p args x) s)) ⟨frame l, μ⟩ T Q :=
  Ends.next _ (Ends.callTo hp h ha hd le_rfl) hT

end

end Light

end
end

section


/-!
# Karatsuba as a fixed program in the benchmark language

The procedure below is a finite `Light.Stmt`, independent of the input
capacity. Recursive products share an eight-capacity scratch area. The
linear-time `half` routine avoids an additional persistent power table.
-/

namespace ThreeSum.LightKaratsuba

open Light
open ThreeSum.Karatsuba
open Polynomial

























































































































section Join

variable {lim : Limits} {P : Program} {d pLinear pFill : ℕ}




































































































































end Join

section BaseCase

variable {lim : Limits} {P : Program} {d : ℕ}






































end BaseCase


















































































theorem ten_temp_le_word (n U : ℕ) (hn : 0 < n) :
    10 * (4 * n * U ^ 2) ≤ wordBound n U := by
  have hn3 : n ≤ n ^ 3 := by nlinarith [Nat.one_le_pow 2 n hn]
  have hu : U ^ 2 ≤ (U + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hm := Nat.mul_le_mul hn3 hu
  unfold wordBound
  nlinarith
























section RecursiveExecution

variable {lim : Limits} {P : Program} {pSelf pHalf pLinear pFill : ℕ}











































































































































end RecursiveExecution

section CompleteProcedure

variable {lim : Limits} {P : Program} {pSelf pHalf pLinear pFill : ℕ}




















































































end CompleteProcedure

end ThreeSum.LightKaratsuba

end

section


/-!
# Costed folding of the verified polynomial product

The ordinary linear array procedure adds coefficients `r` and `r+p` for
each output residue. Its specification is the exact natural cyclic
correlation, including histogram multiplicities.
-/

namespace ThreeSum.LightCyclic

open Light Karatsuba CyclicFold LightKaratsuba

variable {lim : Limits} {P : Program} {d : ℕ}

theorem fold_meets {pLinear : ℕ} (hLinear : P[pLinear]? = some LightArray.linearBody)
    {μ : ℕ → ℤ} {src dst n p U : ℕ} {as bs : List ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hpn : p ≤ n)
    (hsrc : src + 2*n ≤ lim.space) (hdst : dst + p ≤ lim.space)
    (hsep : Apart src (2*n) dst p)
    (ha : as.length ≤ p) (hb : bs.length ≤ p)
    (hA : CoeffBound as (U : ℤ)) (hB : CoeffBound bs (U : ℤ))
    (hprod : ProductAt μ src n (padTo n as) (padTo n bs))
    (hword : 4 * (p : ℤ) * (U : ℤ)^2 ≤ lim.word) :
    Meets lim P pLinear d [src, src+p, dst, p, 1] μ (LightArray.linearTime p)
      fun _ μ' => (∀ r < p, μ' (dst+r) = cyclic p as bs r) ∧
        SameOutside μ μ' dst p := by
  have hfirst (r : ℕ) (hr : r < p) :
      μ (src+r) = (asPolynomial as * asPolynomial bs).coeff r := by
    simpa only [asPolynomial_padTo] using hprod r (by omega)
  have hsecond (r : ℕ) (hr : r < p) :
      μ (src+p+r) = (asPolynomial as * asPolynomial bs).coeff (r+p) := by
    simpa only [asPolynomial_padTo, Nat.add_assoc, Nat.add_comm p r] using
      hprod (r+p) (by omega)
  have hc (r : ℕ) :
      |(asPolynomial as * asPolynomial bs).coeff r| ≤ (2*p*U^2 : ℕ) := by
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
      product_coeff_bound ha hb hA hB r
  have h := LightArray.linear_bounded_meets (d := d) (μ := μ)
    (srcA := src) (srcB := src+p) (dst := dst) (n := p) (U := 2*p*U^2) (c := 1)
    hLinear hw (by omega) (by omega) hdst (Or.inr (by omega)) (Or.inr (by omega))
    (by norm_num) (by push_cast; nlinarith) (by
      intro r hr
      rw [hfirst r hr, hsecond r hr]
      exact ⟨hc r, hc (r+p)⟩)
  apply h.mono le_rfl
  intro res μ' hpost
  refine ⟨?_, hpost.2⟩
  intro r hr
  rw [hpost.1 r hr, one_mul, hfirst r hr, hsecond r hr]
  exact fold_product as bs p r ha hb hr

theorem fold_correlation_meets {pLinear : ℕ}
    (hLinear : P[pLinear]? = some LightArray.linearBody)
    {μ : ℕ → ℤ} {src dst n p U : ℕ} [NeZero p]
    (F H : ZMod p → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hpn : p ≤ n)
    (hsrc : src + 2*n ≤ lim.space) (hdst : dst + p ≤ lim.space)
    (hsep : Apart src (2*n) dst p)
    (hA : CoeffBound (vector p F) (U : ℤ))
    (hB : CoeffBound (vector p (fun z => H (-z))) (U : ℤ))
    (hprod : ProductAt μ src n (padTo n (vector p F))
      (padTo n (vector p (fun z => H (-z)))))
    (hword : 4 * (p : ℤ) * (U : ℤ)^2 ≤ lim.word) :
    Meets lim P pLinear d [src, src+p, dst, p, 1] μ (LightArray.linearTime p)
      fun _ μ' => (∀ r < p, μ' (dst+r) =
        (Balancing.correlation F H (r : ZMod p) : ℤ)) ∧ SameOutside μ μ' dst p := by
  apply (fold_meets hLinear hw hpn hsrc hdst hsep
    (le_of_eq (vector_length _ _)) (le_of_eq (vector_length _ _)) hA hB hprod hword).mono le_rfl
  intro res μ' hpost
  refine ⟨?_, hpost.2⟩
  intro r hr
  rw [hpost.1 r hr]
  exact cyclic_correlation F H r hr









theorem correlation_meets_sourceProof {pThis pMultiply pHalf pLinear pFill : ℕ}
    (hThis : P[pThis]? = some (body pMultiply pLinear))
    (C : LightKaratsuba.Procs P pMultiply pHalf pLinear pFill)
    {μ : ℕ → ℤ} {k a b prod dst work p U : ℕ} [NeZero p]
    (F H : ZMod p → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hpn : p ≤ 2^k)
    (hAseg : Seg μ a (padTo (2^k) (vector p F)))
    (hBseg : Seg μ b (padTo (2^k) (vector p (fun z => H (-z)))))
    (hA : CoeffBound (vector p F) (U : ℤ))
    (hB : CoeffBound (vector p (fun z => H (-z))) (U : ℤ))
    (haf : a + 2^k ≤ work) (hbf : b + 2^k ≤ work)
    (hpf : prod + 2*2^k ≤ work) (hdf : dst+p ≤ work)
    (hsep : Apart prod (2*2^k) dst p)
    (hspace : work+8*2^k ≤ lim.space)
    (hword : (LightKaratsuba.wordBound (2^k) U : ℤ) ≤ lim.word)
    (hd : d+k+2 ≤ lim.depth) :
    Meets lim P pThis d [2^k, a, b, prod, dst, work, p] μ (combinedTime k p)
      fun _ μ' => (∀ r < p, μ' (dst+r) =
        (Balancing.correlation F H (r : ZMod p) : ℤ)) ∧
        (∀ j < work, (j < prod ∨ prod+2*2^k ≤ j) →
          (j < dst ∨ dst+p ≤ j) → μ' j = μ j) := by
  have hn : 0 < (2 : ℕ)^k := Nat.pow_pos (by decide)
  have hAlen : (padTo (2^k) (vector p F)).length = 2^k :=
    padTo_length _ _ (by rw [vector_length]; exact hpn)
  have hBlen : (padTo (2^k) (vector p (fun z => H (-z)))).length = 2^k :=
    padTo_length _ _ (by rw [vector_length]; exact hpn)
  have hfoldword : 4 * (p : ℤ) * (U : ℤ)^2 ≤ lim.word := by
    have ht := LightKaratsuba.ten_temp_le_word (2^k) U hn
    have hpU := Nat.mul_le_mul_right (U^2) (Nat.mul_le_mul_left 4 hpn)
    have ht' : 4*p*U^2 ≤ LightKaratsuba.wordBound (2^k) U := by nlinarith
    exact (by exact_mod_cast ht' : 4 * (p : ℤ) * (U : ℤ)^2 ≤
      (LightKaratsuba.wordBound (2^k) U : ℤ)).trans hword
  apply Meets.of_body hThis
  unfold body combinedTime
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (first
      |
        refine
          Light.Ends.callToThen
            ((LightKaratsuba.meets C hw hAlen hBlen hAseg hBseg
                (coeffBound_padTo hA (2 ^ k)) (coeffBound_padTo hB (2 ^ k)) haf
                hbf hpf hspace hword (d + 1) (by omega))
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (LightKaratsuba.meets C hw hAlen hBlen hAseg hBseg
              (coeffBound_padTo hA (2 ^ k)) (coeffBound_padTo hB (2 ^ k)) haf hbf
              hpf hspace hword (d + 1) (by omega))
            ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
    (on_goal -1 =>
        ((rintro res μ₁ hK); (try with_unfolding_none refine Light.Ends.skip ?_)))
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (first
      |
        refine
          Light.Ends.callToThen
            ((fold_correlation_meets C.linear (μ := μ₁) (n := 2 ^ k) F H hw hpn
                (by omega) (by omega) hsep hA hB hK.1 hfoldword)
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (fold_correlation_meets C.linear (μ := μ₁) (n := 2 ^ k) F H hw hpn
              (by omega) (by omega) hsep hA hB hK.1 hfoldword)
            ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
    (on_goal -1 =>
        ((rintro res₂ μ₂ hF);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  refine ⟨hF.1, ?_⟩
  intro j hj hpj hdj
  exact (hF.2 j hdj).trans (hK.2 j ⟨hj, hpj⟩)










































end ThreeSum.LightCyclic

end


theorem solution : ∀ {lim : Light.Limits} {P : Light.Program} {d pThis pMultiply pHalf pLinear pFill : Nat},
  @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pThis)
      (@Option.some.{0} Light.Stmt (ThreeSum.LightCyclic.body pMultiply pLinear)) →
    ThreeSum.LightKaratsuba.Procs P pMultiply pHalf pLinear pFill →
      ∀ {μ : Nat → Int} {k a b prod dst work p U : Nat}
        [inst : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) p] (F H : ZMod p → Nat),
        @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word →
          @LE.le.{0} Nat instLENat p
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k) →
            Light.Seg μ a
                (ThreeSum.CyclicFold.padTo
                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                    (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k)
                  (ThreeSum.CyclicFold.vector p F)) →
              Light.Seg μ b
                  (ThreeSum.CyclicFold.padTo
                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                      (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k)
                    (ThreeSum.CyclicFold.vector p fun (z : ZMod p) =>
                      H
                        (@Neg.neg.{0} (ZMod p)
                          (@NegZeroClass.toNeg.{0} (ZMod p)
                            (@SubNegZeroMonoid.toNegZeroClass.{0} (ZMod p)
                              (@SubtractionMonoid.toSubNegZeroMonoid.{0} (ZMod p)
                                (@SubtractionCommMonoid.toSubtractionMonoid.{0} (ZMod p)
                                  (@AddCommGroup.toDivisionAddCommMonoid.{0} (ZMod p)
                                    (@Ring.toAddCommGroup.{0} (ZMod p)
                                      (@CommRing.toRing.{0} (ZMod p) (ZMod.commRing p))))))))
                          z))) →
                ThreeSum.Karatsuba.CoeffBound (ThreeSum.CyclicFold.vector p F) (@Nat.cast.{0} Int instNatCastInt U) →
                  ThreeSum.Karatsuba.CoeffBound
                      (ThreeSum.CyclicFold.vector p fun (z : ZMod p) =>
                        H
                          (@Neg.neg.{0} (ZMod p)
                            (@NegZeroClass.toNeg.{0} (ZMod p)
                              (@SubNegZeroMonoid.toNegZeroClass.{0} (ZMod p)
                                (@SubtractionMonoid.toSubNegZeroMonoid.{0} (ZMod p)
                                  (@SubtractionCommMonoid.toSubtractionMonoid.{0} (ZMod p)
                                    (@AddCommGroup.toDivisionAddCommMonoid.{0} (ZMod p)
                                      (@Ring.toAddCommGroup.{0} (ZMod p)
                                        (@CommRing.toRing.{0} (ZMod p) (ZMod.commRing p))))))))
                            z))
                      (@Nat.cast.{0} Int instNatCastInt U) →
                    @LE.le.{0} Nat instLENat
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a
                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k))
                        work →
                      @LE.le.{0} Nat instLENat
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b
                            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k))
                          work →
                        @LE.le.{0} Nat instLENat
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) prod
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                  (@instHPow.{0, 0} Nat Nat
                                    (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k)))
                            work →
                          @LE.le.{0} Nat instLENat
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst p) work →
                            Light.Apart prod
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                    (@instHPow.{0, 0} Nat Nat
                                      (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k))
                                dst p →
                              @LE.le.{0} Nat instLENat
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) work
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                        (@instHPow.{0, 0} Nat Nat
                                          (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k)))
                                  lim.space →
                                @LE.le.{0} Int Int.instLEInt
                                    (@Nat.cast.{0} Int instNatCastInt
                                      (ThreeSum.LightKaratsuba.wordBound
                                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                          (@instHPow.{0, 0} Nat Nat
                                            (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k)
                                        U))
                                    lim.word →
                                  @LE.le.{0} Nat instLENat
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d k)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      lim.depth →
                                    Light.Meets lim P pThis d
                                      (@List.cons.{0} Int
                                        (@HPow.hPow.{0, 0, 0} Int Nat Int
                                          (@instHPow.{0, 0} Int Nat
                                            (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid)))
                                          (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))) k)
                                        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt a)
                                          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt b)
                                            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt prod)
                                              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt dst)
                                                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt work)
                                                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt p)
                                                    (@List.nil.{0} Int))))))))
                                      μ (ThreeSum.LightCyclic.combinedTime k p) fun (x : Int) (μ' : Nat → Int) =>
                                      And
                                        (∀ (r : Nat),
                                          @LT.lt.{0} Nat instLTNat r p →
                                            @Eq.{1} Int
                                              (μ'
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst r))
                                              (@Nat.cast.{0} Int instNatCastInt
                                                (@ThreeSum.Balancing.correlation.{0} (ZMod p)
                                                  (@Ring.toAddCommGroup.{0} (ZMod p)
                                                    (@CommRing.toRing.{0} (ZMod p) (ZMod.commRing p)))
                                                  (@ZMod.fintype p inst) F H
                                                  (@Nat.cast.{0} (ZMod p)
                                                    (@AddMonoidWithOne.toNatCast.{0} (ZMod p)
                                                      (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod p)
                                                        (@Ring.toAddGroupWithOne.{0} (ZMod p)
                                                          (@CommRing.toRing.{0} (ZMod p) (ZMod.commRing p)))))
                                                    r))))
                                        (∀ (j : Nat),
                                          @LT.lt.{0} Nat instLTNat j work →
                                            Or (@LT.lt.{0} Nat instLTNat j prod)
                                                (@LE.le.{0} Nat instLENat
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) prod
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                        (@instHPow.{0, 0} Nat Nat
                                                          (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                        k)))
                                                  j) →
                                              Or (@LT.lt.{0} Nat instLTNat j dst)
                                                  (@LE.le.{0} Nat instLENat
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst
                                                      p)
                                                    j) →
                                                @Eq.{1} Int (μ' j) (μ j)) := by
  exact @ThreeSum.LightCyclic.correlation_meets_sourceProof

#print axioms solution
