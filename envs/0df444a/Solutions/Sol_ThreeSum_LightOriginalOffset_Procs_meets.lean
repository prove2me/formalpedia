-- Prove2me | solution 1 for ThreeSum.LightOriginalOffset.Procs.meets
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T16:40:50.556724+00:00
-- url     : https://prove2.me/submissions/48f3227b-3747-47ac-8b99-db782556199e

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
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle09
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
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Theorems.Thm_ThreeSum_LightBalancedOffset_meets
import Theorems.Thm_ThreeSum_LightCapacity_meets
import Theorems.Thm_ThreeSum_LightResidueHistogram_meets


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.CyclicFold
end ThreeSum.CyclicFold
namespace ThreeSum.Karatsuba
end ThreeSum.Karatsuba
namespace ThreeSum.KaratsubaInterface
end ThreeSum.KaratsubaInterface
namespace ThreeSum.LightHistogram
end ThreeSum.LightHistogram
namespace ThreeSum.LightKaratsuba
end ThreeSum.LightKaratsuba
namespace ThreeSum.LightResidueHistogram
end ThreeSum.LightResidueHistogram
namespace ThreeSum.LightResidues
end ThreeSum.LightResidues

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


















































theorem vector_length (p : ℕ) (f : ZMod p → ℕ) : (vector p f).length = p := by
  simp [vector]

theorem vector_getD (p : ℕ) (f : ZMod p → ℕ) (i : ℕ) (hi : i < p) :
    (vector p f).getD i 0 = (f (i : ZMod p) : ℤ) := by
  rw [List.getD_eq_getElem (vector p f) 0 (by rw [vector_length]; exact hi)]
  simp only [vector, List.getElem_map, List.getElem_range]


































































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

theorem Ends.set {σ T x e} {Q : State → Prop} (hs : e.Safe lim σ) (hT : e.cost + 1 ≤ T)
    (h : Q { σ with loc := Function.update σ.loc x (e.val σ) }) : Ends lim P d (.set x e) σ T Q :=
  ⟨_, _, .set hs, hT, h⟩







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














/-- `x := e`, where e gives z. -/
theorem Ends.setTo {x : ℕ} {e : Expr} (z : ℤ) (h : Q ⟨frame (setLocal l x z), μ⟩)
    (he : e.Gives lim ⟨frame l, μ⟩ z := by (((try have := Light.Std.space_le (by assumption)));
                                                  ((try have := Light.Std.const_le (by assumption)));
                                                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
    (hT : e.cost + 1 ≤ T := by first
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
    Ends lim P d (.set x e) ⟨frame l, μ⟩ T Q := by
  refine Ends.set he.1 hT ?_
  rw [he.2]
  simp only [update_frame_setLocal]
  exact h

/-- `x := e ; s`, where e gives z.  The rest s of the text gets the steps that are left. -/
theorem Ends.setToThen {x : ℕ} {e : Expr} {s : Stmt} (z : ℤ)
    (h : Ends lim P d s ⟨frame (setLocal l x z), μ⟩ (T - (e.cost + 1)) Q)
    (he : e.Gives lim ⟨frame l, μ⟩ z := by (((try have := Light.Std.space_le (by assumption)));
                                                  ((try have := Light.Std.const_le (by assumption)));
                                                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
    (hT : e.cost + 1 ≤ T := by first
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
    Ends lim P d ((Light.Stmt.seq (.set x e) s)) ⟨frame l, μ⟩ T Q :=
  Ends.next _ (Ends.setTo z h he le_rfl) hT



















































































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
# Arbitrary-length interface for the verified multiplication routine

These exact inequalities convert a requested positive coefficient length
to its power-of-two capacity. Polynomial padding preserves the represented
product. The fifth-power bounds include any fixed linear preparation and
folding overhead, so no real-exponent oracle is needed for the time bound.
-/

namespace ThreeSum.KaratsubaInterface

open ThreeSum.Karatsuba ThreeSum.LightKaratsuba Polynomial



theorem le_capacity (p : ℕ) : p ≤ capacity p := Nat.le_pow_clog (by decide) p























































































end ThreeSum.KaratsubaInterface

end

section


/-!
# A linear-time histogram procedure in the benchmark language

The input is an array of already computed residue indices in `[0,p)`.
The output is cleared and incremented once per input item. Multiplicities
are retained, including repeated equal residues.
-/

namespace ThreeSum.LightHistogram

open Light Finset

variable {lim : Limits} {P : Program} {d : ℕ}







theorem count_le (key : ℕ → ℕ) (r i : ℕ) : count key r i ≤ i := by
  exact (Finset.card_filter_le _ _).trans (by simp)






































































































end ThreeSum.LightHistogram

end

section


/-!
# Costed signed residue conversion

This loop uses the benchmark's proved division-free remainder procedure.
Its sign argument supports either an ordinary histogram or a histogram of
the negated original integers. All source multiplicities are retained.
The logarithmic scratch region is reused for each input element.
-/

namespace ThreeSum.LightResidues

open Light

variable {lim : Limits} {P : Program} {d : ℕ}



theorem residue_cast {p : ℕ} (hp : 0 < p) (c x : ℤ) :
    (residue p c x : ℤ) = (c * x) % (p : ℤ) := by
  apply Int.toNat_of_nonneg
  exact Int.emod_nonneg _ (by exact_mod_cast hp.ne')

theorem residue_lt {p : ℕ} (hp : 0 < p) (c x : ℤ) : residue p c x < p := by
  have h := Int.emod_lt_of_pos (c * x) (by exact_mod_cast hp : (0 : ℤ) < p)
  rw [← residue_cast hp] at h
  exact_mod_cast h







































































































end ThreeSum.LightResidues

end

section


/-!
# Original integers to a padded signed histogram

The executable procedure first computes canonical residues of the signed
original integers and then fills the entire requested histogram capacity.
Its postcondition is the precise padded polynomial vector consumed by the
verified cyclic-convolution routine. Repeated input values remain distinct
incidences and contribute their full multiplicity.
-/

namespace ThreeSum.LightResidueHistogram

open Light Finset ThreeSum.LightResidues ThreeSum.LightHistogram
open ThreeSum.CyclicFold ThreeSum.Karatsuba

variable {lim : Limits} {P : Program} {d : ℕ}





/-- Negating the original integers supplies the reversal needed by a
correlation, without a separate reverse-array operation. -/
theorem signedHistogram_neg (p : ℕ) (values : ℕ → ℤ) (n : ℕ) (z : ZMod p) :
    signedHistogram p (-1) values n z = signedHistogram p 1 values n (-z) := by
  simp only [signedHistogram, Histograms.histogram, neg_mul, one_mul, Int.cast_neg,
    neg_eq_iff_eq_neg]








theorem residue_zmod {p : ℕ} (hp : 0 < p) (c x : ℤ) :
    (residue p c x : ZMod p) = ((c * x : ℤ) : ZMod p) := by
  unfold residue
  rw [ZMod.natCast_toNat p (Int.emod_nonneg _ (by exact_mod_cast hp.ne')),
    ZMod.intCast_mod]

theorem residue_eq_iff {p : ℕ} [NeZero p] (c x : ℤ) {r : ℕ} (hr : r < p) :
    residue p c x = r ↔ ((c * x : ℤ) : ZMod p) = (r : ZMod p) := by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  constructor
  · intro h
    rw [← residue_zmod hp, h]
  · intro h
    rw [← residue_zmod hp] at h
    have hv := congrArg ZMod.val h
    simpa only [ZMod.val_natCast_of_lt (residue_lt hp c x),
      ZMod.val_natCast_of_lt hr] using hv

theorem signedHistogram_eq_count {p : ℕ} [NeZero p]
    (c : ℤ) (values : ℕ → ℤ) (n r : ℕ) (hr : r < p) :
    signedHistogram p c values n (r : ZMod p) =
      count (fun i => residue p c (values i)) r n := by
  unfold signedHistogram Histograms.histogram count
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [residue_eq_iff c (values i) hr]

theorem signed_count_zero {p : ℕ} (hp : 0 < p)
    (c : ℤ) (values : ℕ → ℤ) (n r : ℕ) (hr : p ≤ r) :
    count (fun i => residue p c (values i)) r n = 0 := by
  unfold count
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro i hi heq
  change residue p c (values i) = r at heq
  have h := residue_lt hp c (values i)
  omega

/-- This equality holds at every index, including the zero padding. -/
theorem padded_histogram_getD {p : ℕ} [NeZero p]
    (c : ℤ) (values : ℕ → ℤ) (n cap r : ℕ) :
    (padTo cap (vector p (signedHistogram p c values n))).getD r 0 =
      (count (fun i => residue p c (values i)) r n : ℤ) := by
  rw [← asPolynomial_coeff, asPolynomial_padTo, asPolynomial_coeff]
  by_cases hr : r < p
  · rw [vector_getD _ _ _ hr, signedHistogram_eq_count c values n r hr]
  · rw [List.getD_eq_default _ _ (by rw [vector_length]; omega)]
    rw [signed_count_zero (Nat.pos_of_ne_zero (NeZero.ne p)) c values n r (by omega)]
    rfl

theorem padded_histogram_bound {p : ℕ} [NeZero p]
    (c : ℤ) (values : ℕ → ℤ) (n cap : ℕ) :
    CoeffBound (padTo cap (vector p (signedHistogram p c values n))) (n : ℤ) := by
  intro r
  rw [padded_histogram_getD, abs_of_nonneg (Int.natCast_nonneg _)]
  exact_mod_cast count_le (fun i => residue p c (values i)) r n





















































































end ThreeSum.LightResidueHistogram

end

section


/-!
# Modular triple counts from the original integer arrays

This interface identifies the executable histogram/correlation lookup with
the exact `Arithmetic.modCount` used in the weighted false-triple argument.
The three indices retain their multiplicities even when input values repeat.
-/

namespace ThreeSum.ModuloCounts

open Finset LightResidueHistogram
open scoped BigOperators
















































theorem signedHistogram_congr {p c n} {a b : ℕ → ℤ}
    (hab : ∀ i < n, a i = b i) :
    signedHistogram p c a n = signedHistogram p c b n := by
  funext z
  unfold signedHistogram Histograms.histogram
  apply sum_congr rfl
  intro i hi
  simp only [hab i (mem_range.mp hi)]











end ThreeSum.ModuloCounts

end

section


/-!
# An actual common offset from two original signed key arrays

The fixed program builds both padded histograms, including reversal, from
the supplied integer keys. It computes its own power-of-two capacity and
chooses the least correlation minimum with the checked fast multiplication.
Repeated keys count separately. No histogram or capacity table is supplied.
-/

namespace ThreeSum.LightOriginalOffset

open Light LightResidues LightResidueHistogram
open KaratsubaInterface CyclicFold
open scoped BigOperators

set_option maxHeartbeats 1800000
set_option maxRecDepth 8000




































































variable {lim : Limits} {P : Program} {d : ℕ}

theorem Procs.meets_sourceProof {pMain a b nLeft nRight p N free U : ℕ} [NeZero p]
    {μ : ℕ → ℤ} (C : Procs P pMain)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (ha : a+nLeft ≤ free) (hb : b+nRight ≤ free)
    (hnLeft : nLeft ≤ N) (hnRight : nRight ≤ N)
    (hspace : space free p N U ≤ lim.space) (hword : (word p N U : ℤ) ≤ lim.word)
    (hd : d+Nat.clog 2 p+4 ≤ lim.depth)
    (hLeft : ∀ i < nLeft, |μ (a+i)| ≤ (U : ℤ))
    (hRight : ∀ i < nRight, |μ (b+i)| ≤ (U : ℤ)) :
    Meets lim P pMain d [a,b,nLeft,nRight,p,N,free] μ (time p nLeft nRight U)
      (fun r ν => r = (selected p (fun i => μ (a+i)) (fun i => μ (b+i)) nLeft nRight : ℤ) ∧
        Kept μ ν free) := by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  let q := capacity p
  have hq : 0 < q := Nat.pow_pos (by decide)
  have hpq : p ≤ q := le_capacity p
  have hspace' : free+13*q+N+Nat.log 2 (U+1)+2 ≤ lim.space := hspace
  have hkw : (LightKaratsuba.wordBound q N : ℤ) ≤ lim.word := by
    exact (Int.ofNat_le.mpr (show LightKaratsuba.wordBound q N ≤ word p N U by
      unfold word; change LightKaratsuba.wordBound (capacity p) N ≤ _; omega)).trans hword
  have hew : (4*U+4*p+16 : ℤ) ≤ lim.word := by
    have hh : 4*U+4*p+16 ≤ word p N U := by unfold word; omega
    exact_mod_cast (Int.ofNat_le.mpr hh).trans hword
  have hcw : ((2*p+1 : ℕ) : ℤ) ≤ lim.word := by push_cast; omega
  let F := signedHistogram p 1 (fun i => μ (b+i)) nRight
  let H := signedHistogram p 1 (fun i => μ (a+i)) nLeft
  have hHneg : signedHistogram p (-1) (fun i => μ (a+i)) nLeft = (fun z => H (-z)) := by
    funext z
    exact signedHistogram_neg p _ _ z
  have hFbound : Karatsuba.CoeffBound (vector p F) (N : ℤ) := by
    have hh := padded_histogram_bound (p := p) 1 (fun i => μ (b+i)) nRight 0
    simp only [padTo,Nat.zero_sub,List.replicate_zero,List.append_nil] at hh
    intro i
    exact (hh i).trans (Int.ofNat_le.mpr hnRight)
  have hHbound : Karatsuba.CoeffBound (vector p (fun z => H (-z))) (N : ℤ) := by
    have hh := padded_histogram_bound (p := p) (-1) (fun i => μ (a+i)) nLeft 0
    simp only [padTo,Nat.zero_sub,List.replicate_zero,List.append_nil] at hh
    rw [hHneg] at hh
    intro i
    exact (hh i).trans (Int.ofNat_le.mpr hnLeft)
  apply Meets.of_body C.main
  unfold body time
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
            ((LightCapacity.meets C.capacityProc μ hp hcw) _ (by omega)) ?_ ?_ ?_
            ?_
      |
        refine
          Light.Ends.callToThen (LightCapacity.meets C.capacityProc μ hp hcw) ?_
            ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, q,
                capacity]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [q, capacity] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, q, capacity] <;> omega)));
    (on_goal -1 =>
        ((rintro capVal μ₀ ⟨hcapacity, hmem⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  subst μ₀
  subst capVal
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (free + q) ?_ ?_ ?_);
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
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (free + 2 * q) ?_ ?_ ?_);
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
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (free + 3 * q) ?_ ?_ ?_);
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
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (free + 5 * q) ?_ ?_ ?_);
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
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (free + 5 * q + N) ?_ ?_ ?_);
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
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
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
            ((LightResidueHistogram.meets (d := d + 1) (src := a) (dst :=
                free + 2 * q) (codes := free + 5 * q) (work := free + 5 * q + N)
                (cap := q) (c := -1) C.histogram C.residues C.emod C.count
                C.karatsuba.fill hw (by omega) hp hpq (by omega) (by omega)
                (by omega) (by omega) (by norm_num) hew hLeft)
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (LightResidueHistogram.meets (d := d + 1) (src := a) (dst :=
              free + 2 * q) (codes := free + 5 * q) (work := free + 5 * q + N)
              (cap := q) (c := -1) C.histogram C.residues C.emod C.count
              C.karatsuba.fill hw (by omega) hp hpq (by omega) (by omega)
              (by omega) (by omega) (by norm_num) hew hLeft)
            ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, q,
                capacity]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [q, capacity] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, q, capacity] <;> omega)));
    (on_goal -1 =>
        ((rintro _ μ₁ ⟨hLeftSeg, hkeep₁⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  rw [hHneg] at hLeftSeg
  have hRightRead (i : ℕ) (hi : i < nRight) : μ₁ (b+i) = μ (b+i) :=
    hkeep₁ _ ⟨by omega,Or.inl (by omega)⟩
  have hRight₁ : ∀ i < nRight, |μ₁ (b+i)| ≤ (U : ℤ) := by
    intro i hi
    rw [hRightRead i hi]
    exact hRight i hi
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
            ((LightResidueHistogram.meets (d := d + 1) (src := b) (dst :=
                free + q) (codes := free + 5 * q) (work := free + 5 * q + N)
                (cap := q) (c := 1) C.histogram C.residues C.emod C.count
                C.karatsuba.fill hw (by omega) hp hpq (by omega) (by omega)
                (by omega) (by omega) (by norm_num) hew hRight₁)
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (LightResidueHistogram.meets (d := d + 1) (src := b) (dst := free + q)
              (codes := free + 5 * q) (work := free + 5 * q + N) (cap := q) (c :=
              1) C.histogram C.residues C.emod C.count C.karatsuba.fill hw
              (by omega) hp hpq (by omega) (by omega) (by omega) (by omega)
              (by norm_num) hew hRight₁)
            ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, q,
                capacity]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [q, capacity] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, q, capacity] <;> omega)));
    (on_goal -1 =>
        ((rintro _ μ₂ ⟨hRightSeg, hkeep₂⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  rw [ModuloCounts.signedHistogram_congr (p := p) (c := 1) hRightRead] at hRightSeg
  have hLeftSeg₂ : Seg μ₂ (free+2*q) (padTo q (vector p (fun z => H (-z)))) := by
    intro i hi
    have hlen : (padTo q (vector p (fun z => H (-z)))).length = q :=
      padTo_length _ _ (by rw [vector_length]; exact hpq)
    have hiq : i < q := by omega
    rw [hkeep₂ _ ⟨by omega,Or.inr (by omega)⟩]
    exact hLeftSeg i hi
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
            ((LightBalancedOffset.meets (d := d + 1) (k := Nat.clog 2 p) (a :=
                free + q) (b := free + 2 * q) (prod := free + 3 * q) (dst := free)
                (work := free + 5 * q + N) C.offset C.cyclic C.minimum C.karatsuba
                F H hw hpq hRightSeg hLeftSeg₂ hFbound hHbound
                (by (change free + q + q ≤ free + 5 * q + N); (omega))
                (by (change free + 2 * q + q ≤ free + 5 * q + N); (omega))
                (by (change free + 3 * q + 2 * q ≤ free + 5 * q + N); (omega))
                (by omega) (by (right); (change free + p ≤ free + 3 * q); (omega))
                (by (change free + 5 * q + N + 8 * q ≤ lim.space); (omega)) hkw
                (by omega))
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (LightBalancedOffset.meets (d := d + 1) (k := Nat.clog 2 p) (a :=
              free + q) (b := free + 2 * q) (prod := free + 3 * q) (dst := free)
              (work := free + 5 * q + N) C.offset C.cyclic C.minimum C.karatsuba F
              H hw hpq hRightSeg hLeftSeg₂ hFbound hHbound
              (by (change free + q + q ≤ free + 5 * q + N); (omega))
              (by (change free + 2 * q + q ≤ free + 5 * q + N); (omega))
              (by (change free + 3 * q + 2 * q ≤ free + 5 * q + N); (omega))
              (by omega) (by (right); (change free + p ≤ free + 3 * q); (omega))
              (by (change free + 5 * q + N + 8 * q ≤ lim.space); (omega)) hkw
              (by omega))
            ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, q,
                capacity]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [q, capacity] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, q, capacity] <;> omega)));
    (on_goal -1 =>
        ((rintro result μ₃ ⟨hresult, hkeep₃⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  refine ⟨hresult,?_⟩
  intro i hi
  change μ₃ i = μ i
  rw [hkeep₃ i (by omega) (Or.inl (by omega)) (Or.inl (by omega))]
  exact (hkeep₂ i ⟨by omega,Or.inl (by omega)⟩).trans
    (hkeep₁ i ⟨by omega,Or.inl (by omega)⟩)











































end ThreeSum.LightOriginalOffset

end


theorem solution : ∀ {lim : Light.Limits} {P : Light.Program} {d pMain a b nLeft nRight p N free U : Nat}
  [inst : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) p] {μ : Nat → Int}
  (C : ThreeSum.LightOriginalOffset.Procs P pMain),
  @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word →
    @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a nLeft) free →
      @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b nRight) free →
        @LE.le.{0} Nat instLENat nLeft N →
          @LE.le.{0} Nat instLENat nRight N →
            @LE.le.{0} Nat instLENat (ThreeSum.LightOriginalOffset.space free p N U) lim.space →
              @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightOriginalOffset.word p N U))
                  lim.word →
                @LE.le.{0} Nat instLENat
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
                        (Nat.clog (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) p))
                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                    lim.depth →
                  (∀ (i : Nat),
                      @LT.lt.{0} Nat instLTNat i nLeft →
                        @LE.le.{0} Int Int.instLEInt
                          (@abs.{0} Int instLatticeInt Int.instAddGroup
                            (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a i)))
                          (@Nat.cast.{0} Int instNatCastInt U)) →
                    (∀ (i : Nat),
                        @LT.lt.{0} Nat instLTNat i nRight →
                          @LE.le.{0} Int Int.instLEInt
                            (@abs.{0} Int instLatticeInt Int.instAddGroup
                              (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b i)))
                            (@Nat.cast.{0} Int instNatCastInt U)) →
                      Light.Meets lim P pMain d
                        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt a)
                          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt b)
                            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt nLeft)
                              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt nRight)
                                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt p)
                                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt N)
                                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt free)
                                      (@List.nil.{0} Int))))))))
                        μ (ThreeSum.LightOriginalOffset.time p nLeft nRight U) fun (r : Int) (ν : Nat → Int) =>
                        And
                          (@Eq.{1} Int r
                            (@Nat.cast.{0} Int instNatCastInt
                              (@ThreeSum.LightOriginalOffset.selected p inst
                                (fun (i : Nat) =>
                                  μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a i))
                                (fun (i : Nat) =>
                                  μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b i))
                                nLeft nRight)))
                          (Light.Kept μ ν free) := by
  exact @ThreeSum.LightOriginalOffset.Procs.meets_sourceProof

#print axioms solution
