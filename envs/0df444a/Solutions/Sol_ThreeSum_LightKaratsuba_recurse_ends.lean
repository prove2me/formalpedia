-- Prove2me | solution 1 for ThreeSum.LightKaratsuba.recurse_ends
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T16:21:36.716185+00:00
-- url     : https://prove2.me/submissions/2648a664-f9c3-4e16-9e6b-ce942e8ae65b

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
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
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
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorems.Thm_Light_half_meets
import Theorems.Thm_ThreeSum_Karatsuba_product_coeff_bound
import Theorems.Thm_ThreeSum_LightArray_linear_bounded_meets
import Theorems.Thm_ThreeSum_LightKaratsuba_join_ends
import Theorems.Thm_ThreeSum_LightKaratsuba_joined_product


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.Karatsuba
end ThreeSum.Karatsuba
namespace ThreeSumApsp
end ThreeSumApsp

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
















@[simp] theorem length_plus (as bs : List ℤ) :
    (plus as bs).length = max as.length bs.length := by
  induction as generalizing bs with
  | nil => simp [plus]
  | cons a as ih =>
    cases bs with
    | nil => simp [plus]
    | cons b bs => simpa [plus, Nat.succ_max_succ] using congrArg Nat.succ (ih bs)












@[simp] theorem asPolynomial_plus (as bs : List ℤ) :
    asPolynomial (plus as bs) = asPolynomial as + asPolynomial bs := by
  induction as generalizing bs with
  | nil => simp [plus, asPolynomial]
  | cons a as ih =>
    cases bs with
    | nil => simp [plus, asPolynomial]
    | cons b bs =>
      simp only [plus, asPolynomial, ih, map_add]
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

@[simp] theorem plus_getD (as bs : List ℤ) (j : ℕ) :
    (plus as bs).getD j 0 = as.getD j 0 + bs.getD j 0 := by
  simpa only [asPolynomial_coeff, Polynomial.coeff_add] using
    congrArg (fun p : Polynomial ℤ => p.coeff j) (asPolynomial_plus as bs)








theorem coeffBound_nonneg {as : List ℤ} {U : ℤ} (h : CoeffBound as U) : 0 ≤ U :=
  (abs_nonneg _).trans (h 0)

theorem CoeffBound.of_mem {as : List ℤ} {U : ℤ} (hU : 0 ≤ U)
    (hm : ∀ x ∈ as, |x| ≤ U) : CoeffBound as U := by
  intro j
  by_cases hj : j < as.length
  · rw [List.getD_eq_getElem _ _ hj]
    exact hm _ (List.getElem_mem hj)
  · rw [List.getD_eq_default _ _ (by omega), abs_zero]
    exact hU

theorem CoeffBound.mem {as : List ℤ} {U x : ℤ} (h : CoeffBound as U)
    (hx : x ∈ as) : |x| ≤ U := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
  simpa only [List.getD_eq_getElem _ _ hj] using h j

theorem CoeffBound.take {as : List ℤ} {U : ℤ} (h : CoeffBound as U) (n : ℕ) :
    CoeffBound (as.take n) U :=
  .of_mem (coeffBound_nonneg h) (fun x hx => h.mem (List.mem_of_mem_take hx))

theorem CoeffBound.drop {as : List ℤ} {U : ℤ} (h : CoeffBound as U) (n : ℕ) :
    CoeffBound (as.drop n) U :=
  .of_mem (coeffBound_nonneg h) (fun x hx => h.mem (List.mem_of_mem_drop hx))

theorem CoeffBound.plus {as bs : List ℤ} {U V : ℤ}
    (ha : CoeffBound as U) (hb : CoeffBound bs V) : CoeffBound (plus as bs) (U + V) := by
  intro j
  rw [plus_getD]
  exact (abs_add_le _ _).trans (add_le_add (ha j) (hb j))





















































end ThreeSum.Karatsuba

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
# Segments of the memory

Seg μ a l says that the cells a, a + 1, …, a + l.length - 1 of the memory μ hold the list l.
SegN is Seg for a list of natural numbers, MatAt for a matrix written row by row, VecAt for a vector
of indices.  The file has the lemmas for reading a cell of a segment, writing into it, writing
elsewhere, and for cutting and joining segments.  Each of the four predicates has its lemma `keep`,
which carries it to a later memory.
-/

@[expose] public section

namespace Light

open ThreeSumApsp







variable {μ μ' μ'' : ℕ → ℤ} {a b n : ℕ} {l l₁ l₂ : List ℤ} {x : ℤ}























































theorem Seg.take (h : Seg μ a l) (k : ℕ) : Seg μ a (l.take k) := fun i hi => by
  have hi' : i < l.length := by simp at hi; omega
  rw [List.getElem_take, h i hi']

theorem Seg.drop (h : Seg μ a l) (k : ℕ) : Seg μ (a + k) (l.drop k) := fun i hi => by
  have hi' : k + i < l.length := by simp at hi; omega
  rw [List.getElem_drop, ← h _ hi', Nat.add_assoc]

/-- A segment only depends on its own cells. -/
theorem Seg.congr (h : Seg μ a l) (he : ∀ i < l.length, μ' (a + i) = μ (a + i)) : Seg μ' a l :=
  fun i hi => by rw [he i hi, h i hi]

































































































































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































































theorem wordBound_monoU {n U V : ℕ} (hUV : U ≤ V) : wordBound n U ≤ wordBound n V := by
  unfold wordBound
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega : U + 1 ≤ V + 1) 2)

theorem wordBound_child (m U : ℕ) : wordBound m (2 * U) ≤ wordBound (2 * m) U := by
  unfold wordBound
  have hu : (2 * U + 1) ^ 2 ≤ (2 * (U + 1)) ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  calc
    _ ≤ 128 * m ^ 3 * (2 * (U + 1)) ^ 2 := Nat.mul_le_mul_left _ hu
    _ ≤ _ := by ring_nf; omega

theorem wordBound_ge_twice (n U : ℕ) (hn : 0 < n) : 2 * U ≤ wordBound n U := by
  have hn3 : 1 ≤ n ^ 3 := Nat.one_le_pow _ _ hn
  have hu : U ≤ (U + 1) ^ 2 := by nlinarith
  have hm := Nat.mul_le_mul_left ((U + 1) ^ 2) hn3
  unfold wordBound
  nlinarith

theorem ten_temp_le_word (n U : ℕ) (hn : 0 < n) :
    10 * (4 * n * U ^ 2) ≤ wordBound n U := by
  have hn3 : n ≤ n ^ 3 := by nlinarith [Nat.one_le_pow 2 n hn]
  have hu : U ^ 2 ≤ (U + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hm := Nat.mul_le_mul hn3 hu
  unfold wordBound
  nlinarith

theorem linear_plus_segment {μ μ' : ℕ → ℤ} {a b out n : ℕ} {as bs : List ℤ}
    (ha : Seg μ a as) (hb : Seg μ b bs) (hAlen : as.length = n) (hBlen : bs.length = n)
    (hwrite : ∀ i < n, μ' (out + i) = μ (a + i) + 1 * μ (b + i)) :
    Seg μ' out (plus as bs) := by
  intro i hi
  have hin : i < n := by simpa only [length_plus, hAlen, hBlen, max_self] using hi
  rw [← List.getD_eq_getElem _ 0 hi, plus_getD,
    ← ha.getD (by omega : i < as.length) 0, ← hb.getD (by omega : i < bs.length) 0]
  simpa only [one_mul] using hwrite i hin

theorem ProductAt.bound {μ : ℕ → ℤ} {out n : ℕ} {as bs : List ℤ} {U : ℤ}
    (hp : ProductAt μ out n as bs) (ha : as.length ≤ n) (hb : bs.length ≤ n)
    (hA : CoeffBound as U) (hB : CoeffBound bs U) :
    ∀ j < 2 * n, |μ (out + j)| ≤ 2 * (n : ℤ) * U ^ 2 := by
  intro j hj
  rw [hp j hj]
  exact product_coeff_bound ha hb hA hB j

theorem ProductAt.congr {μ μ' : ℕ → ℤ} {out n : ℕ} {as bs : List ℤ}
    (hp : ProductAt μ out n as bs)
    (he : ∀ j < 2 * n, μ' (out + j) = μ (out + j)) :
    ProductAt μ' out n as bs := fun j hj => (he j hj).trans (hp j hj)

section RecursiveExecution

variable {lim : Limits} {P : Program} {pSelf pHalf pLinear pFill : ℕ}

set_option maxHeartbeats 2000000 in
theorem recurse_ends_sourceProof (C : Procs P pSelf pHalf pLinear pFill)
    {d k m a b out work U : ℕ} {as bs : List ℤ} {μ : ℕ → ℤ}
    (hmPow : m = 2 ^ k) (hw : (lim.space : ℤ) ≤ lim.word)
    (hAlen : as.length = 2 * m) (hBlen : bs.length = 2 * m)
    (hAseg : Seg μ a as) (hBseg : Seg μ b bs)
    (hA : CoeffBound as (U : ℤ)) (hB : CoeffBound bs (U : ℤ))
    (haf : a + 2 * m ≤ work) (hbf : b + 2 * m ≤ work)
    (hof : out + 2 * (2 * m) ≤ work) (hspace : work + 8 * (2 * m) ≤ lim.space)
    (hword : (wordBound (2 * m) U : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (ih : ∀ (a' b' out' work' U' : ℕ) (as' bs' : List ℤ) (μ' : ℕ → ℤ),
      as'.length = m → bs'.length = m → Seg μ' a' as' → Seg μ' b' bs' →
      CoeffBound as' (U' : ℤ) → CoeffBound bs' (U' : ℤ) →
      a' + m ≤ work' → b' + m ≤ work' → out' + 2 * m ≤ work' →
      work' + 8 * m ≤ lim.space → (wordBound m U' : ℤ) ≤ lim.word →
      Meets lim P pSelf (d + 1) [m, a', b', out', work'] μ' (time k)
        (fun _ μ'' => Result μ' out' m work' as' bs' μ'')) :
    Ends lim P d (recurseBody pSelf pHalf pLinear pFill)
      ⟨frame [2 * m, a, b, out, work], μ⟩ (time (k + 1) - 4)
      (fun σ' => Result μ out (2 * m) work as bs σ'.mem) := by
  have hm : 0 < m := hmPow ▸ Nat.pow_pos (by decide)
  have hAU0 := hA.take m
  have hAU1 := hA.drop m
  have hBU0 := hB.take m
  have hBU1 := hB.drop m
  have hAs : CoeffBound (plus (as.take m) (as.drop m)) ((2 * U : ℕ) : ℤ) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat, two_mul, Nat.cast_add] using hAU0.plus hAU1
  have hBs : CoeffBound (plus (bs.take m) (bs.drop m)) ((2 * U : ℕ) : ℤ) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat, two_mul, Nat.cast_add] using hBU0.plus hBU1
  have ha0 : (as.take m).length = m := by simp only [List.length_take, hAlen]; omega
  have ha1 : (as.drop m).length = m := by simp only [List.length_drop, hAlen]; omega
  have hb0 : (bs.take m).length = m := by simp only [List.length_take, hBlen]; omega
  have hb1 : (bs.drop m).length = m := by simp only [List.length_drop, hBlen]; omega
  have has : (plus (as.take m) (as.drop m)).length = m := by simp only [length_plus, ha0, ha1, max_self]
  have hbs : (plus (bs.take m) (bs.drop m)).length = m := by simp only [length_plus, hb0, hb1, max_self]
  have hword2 : 2 * (U : ℤ) ≤ lim.word := by
    have hh : 2 * (U : ℤ) ≤ wordBound (2 * m) U := by
      exact_mod_cast wordBound_ge_twice (2 * m) U (by omega)
    exact hh.trans hword
  have hchild2 : (wordBound m (2 * U) : ℤ) ≤ lim.word := by
    have hc : (wordBound m (2 * U) : ℤ) ≤ wordBound (2 * m) U := by
      exact_mod_cast wordBound_child m U
    exact hc.trans hword
  have hchild1 : (wordBound m U : ℤ) ≤ lim.word := by
    have hc : (wordBound m U : ℤ) ≤ wordBound m (2 * U) := by
      exact_mod_cast wordBound_monoU (n := m) (by omega : U ≤ 2 * U)
    exact hc.trans hchild2
  have hhalfeq : (2 * m + 1) / 2 = m := by omega
  have hhalfword : ((2 * m + 1 : ℕ) : ℤ) ≤ lim.word := by
    have hh : ((2 * m + 1 : ℕ) : ℤ) ≤ lim.space := by exact_mod_cast (show 2 * m + 1 ≤ lim.space by omega)
    exact hh.trans hw
  have hhalf := half_meets (lim := lim) (d := d + 1) C.half μ (h := 2 * m) hhalfword
  simp only [halfTime, hhalfeq] at hhalf
  unfold recurseBody
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
      | refine Light.Ends.callToThen (hhalf _ (by omega)) ?_ ?_ ?_ ?_
      | refine Light.Ends.callToThen hhalf ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, time] <;> omega)));
    (on_goal -1 =>
        ((rintro _ μ₀ ⟨rfl, hμ₀⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  subst μ₀
  have hsA0 := hAseg.take m
  have hsA1 := hAseg.drop m
  have hsumA := LightArray.linear_bounded_meets (d := d + 1) C.linear
    (μ := μ) (srcA := a) (srcB := a + m) (dst := work + 3 * (2 * m))
    (n := m) (U := U) (c := 1) hw (by omega) (by omega) (by omega)
    (Or.inr (by omega)) (Or.inr (by omega)) (by norm_num) hword2
    (fun i hi => ⟨by rw [hsA0.getD (by omega) 0]; exact hAU0 i,
      by rw [hsA1.getD (by omega) 0]; exact hAU1 i⟩)
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
      | refine Light.Ends.callToThen (hsumA _ (by omega)) ?_ ?_ ?_ ?_
      | refine Light.Ends.callToThen hsumA ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, time,
                LightArray.linearTime]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [time, LightArray.linearTime] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, time,
                LightArray.linearTime] <;>
              omega)));
    (on_goal -1 =>
        ((rintro _ μ₁ ⟨hrA, hkA⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  have hsuma := linear_plus_segment hsA0 hsA1 ha0 ha1 hrA
  have hBseg1 : Seg μ₁ b bs := hBseg.congr (fun i hi => hkA _ (by omega))
  have hsB0 := hBseg1.take m
  have hsB1 := hBseg1.drop m
  have hsumB := LightArray.linear_bounded_meets (d := d + 1) C.linear
    (μ := μ₁) (srcA := b) (srcB := b + m) (dst := work + 3 * (2 * m) + m)
    (n := m) (U := U) (c := 1) hw (by omega) (by omega) (by omega)
    (Or.inr (by omega)) (Or.inr (by omega)) (by norm_num) hword2
    (fun i hi => ⟨by rw [hsB0.getD (by omega) 0]; exact hBU0 i,
      by rw [hsB1.getD (by omega) 0]; exact hBU1 i⟩)
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
      | refine Light.Ends.callToThen (hsumB _ (by omega)) ?_ ?_ ?_ ?_
      | refine Light.Ends.callToThen hsumB ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, time,
                LightArray.linearTime]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [time, LightArray.linearTime] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, time,
                LightArray.linearTime] <;>
              omega)));
    (on_goal -1 =>
        ((rintro _ μ₂ ⟨hrB, hkB⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  have hsumb := linear_plus_segment hsB0 hsB1 hb0 hb1 hrB
  have hsuma2 : Seg μ₂ (work + 3 * (2 * m)) (plus (as.take m) (as.drop m)) :=
    hsuma.congr (fun i hi => hkB _ (by omega))
  have hAseg2 : Seg μ₂ a as := hAseg.congr (fun i hi => (hkB _ (by omega)).trans (hkA _ (by omega)))
  have hBseg2 : Seg μ₂ b bs := hBseg1.congr (fun i hi => hkB _ (by omega))
  have hprod0 := ih a b work (work + 4 * (2 * m)) U (as.take m) (bs.take m) μ₂
    ha0 hb0 (hAseg2.take m) (hBseg2.take m) hAU0 hBU0
    (by omega) (by omega) (by omega) (by omega) hchild1
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
      | refine Light.Ends.callToThen (hprod0 _ (by omega)) ?_ ?_ ?_ ?_
      | refine Light.Ends.callToThen hprod0 ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, time,
                LightArray.linearTime]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [time, LightArray.linearTime] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, time,
                LightArray.linearTime] <;>
              omega)));
    (on_goal -1 =>
        ((rintro _ μ₃ ⟨hp0, hkp0⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  have hAseg3 : Seg μ₃ a as := hAseg2.congr (fun i hi => hkp0 _ ⟨by omega, by omega⟩)
  have hBseg3 : Seg μ₃ b bs := hBseg2.congr (fun i hi => hkp0 _ ⟨by omega, by omega⟩)
  have hprod2 := ih (a + m) (b + m) (work + 2 * m) (work + 4 * (2 * m)) U
    (as.drop m) (bs.drop m) μ₃ ha1 hb1 (hAseg3.drop m) (hBseg3.drop m) hAU1 hBU1
    (by omega) (by omega) (by omega) (by omega) hchild1
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
      | refine Light.Ends.callToThen (hprod2 _ (by omega)) ?_ ?_ ?_ ?_
      | refine Light.Ends.callToThen hprod2 ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, time,
                LightArray.linearTime]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [time, LightArray.linearTime] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, time,
                LightArray.linearTime] <;>
              omega)));
    (on_goal -1 =>
        ((rintro _ μ₄ ⟨hp2, hkp2⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  have hp04 : ProductAt μ₄ work m (as.take m) (bs.take m) :=
    hp0.congr (fun j hj => hkp2 _ ⟨by omega, by omega⟩)
  have hsuma4 : Seg μ₄ (work + 3 * (2 * m)) (plus (as.take m) (as.drop m)) :=
    hsuma2.congr (fun i hi =>
      (hkp2 _ ⟨by omega, by omega⟩).trans (hkp0 _ ⟨by omega, by omega⟩))
  have hsumb4 : Seg μ₄ (work + 3 * (2 * m) + m) (plus (bs.take m) (bs.drop m)) :=
    hsumb.congr (fun i hi =>
      (hkp2 _ ⟨by omega, by omega⟩).trans (hkp0 _ ⟨by omega, by omega⟩))
  have hprodm := ih (work + 3 * (2 * m)) (work + 3 * (2 * m) + m)
    (work + 2 * (2 * m)) (work + 4 * (2 * m)) (2 * U)
    (plus (as.take m) (as.drop m)) (plus (bs.take m) (bs.drop m)) μ₄
    has hbs hsuma4 hsumb4 hAs hBs
    (by omega) (by omega) (by omega) (by omega) hchild2
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
      | refine Light.Ends.callToThen (hprodm _ (by omega)) ?_ ?_ ?_ ?_
      | refine Light.Ends.callToThen hprodm ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, time,
                LightArray.linearTime]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [time, LightArray.linearTime] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, time,
                LightArray.linearTime] <;>
              omega)));
    (on_goal -1 =>
        ((rintro _ μ₅ ⟨hpm, hkpm⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  have hp05 : ProductAt μ₅ work m (as.take m) (bs.take m) :=
    hp04.congr (fun j hj => hkpm _ ⟨by omega, by omega⟩)
  have hp25 : ProductAt μ₅ (work + 2 * m) m (as.drop m) (bs.drop m) :=
    hp2.congr (fun j hj => hkpm _ ⟨by omega, by omega⟩)
  have htword : 10 * ((4 * (2 * m) * U ^ 2 : ℕ) : ℤ) ≤ lim.word := by
    have hh : 10 * ((4 * (2 * m) * U ^ 2 : ℕ) : ℤ) ≤ wordBound (2 * m) U := by
      exact_mod_cast ten_temp_le_word (2 * m) U (by omega)
    exact hh.trans hword
  have htemp : ∀ i < 2 * m,
      |μ₅ (work + i)| ≤ (4 * (2 * m) * U ^ 2 : ℕ) ∧
      |μ₅ (work + 2 * m + i)| ≤ (4 * (2 * m) * U ^ 2 : ℕ) ∧
      |μ₅ (work + 2 * (2 * m) + i)| ≤ (4 * (2 * m) * U ^ 2 : ℕ) := by
    intro i hi
    have h₀ := hp05.bound ha0.le hb0.le hAU0 hBU0 i hi
    have h₂ := hp25.bound ha1.le hb1.le hAU1 hBU1 i hi
    have hₘ := hpm.bound has.le hbs.le hAs hBs i hi
    push_cast at hₘ ⊢
    constructor
    · nlinarith [sq_nonneg (U : ℤ)]
    constructor
    · nlinarith [sq_nonneg (U : ℤ)]
    · nlinarith
  refine (join_ends C.linear C.fill (n := 2 * m) (half := m) (U := 4 * (2 * m) * U ^ 2)
    (by omega) rfl hw hof (by omega) htword htemp hd).mono
      (by first
          |
            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, time,
                  joinTime, LightArray.linearTime]);
              (first
                | omega
                | ((ring_nf); (omega))))
          | omega
          |
            (simp [time, joinTime, LightArray.linearTime] <;>
                first
                | omega
                | ((ring_nf); (omega)))) ?_
  intro σ' hj
  constructor
  · intro j hjj
    exact (hj.1 j hjj).trans (joined_product rfl hAlen hBlen hp05 hp25 hpm j)
  · intro j hjj
    rw [hj.2 j hjj, hkpm j ⟨by omega, by omega⟩, hkp2 j ⟨by omega, by omega⟩,
      hkp0 j ⟨by omega, by omega⟩, hkB j (by omega), hkA j (by omega)]

end RecursiveExecution

section CompleteProcedure

variable {lim : Limits} {P : Program} {pSelf pHalf pLinear pFill : ℕ}




















































































end CompleteProcedure

end ThreeSum.LightKaratsuba

end


theorem solution : ∀ {lim : Light.Limits} {P : Light.Program} {pSelf pHalf pLinear pFill : Nat},
  ThreeSum.LightKaratsuba.Procs P pSelf pHalf pLinear pFill →
    ∀ {d k m a b out work U : Nat} {as bs : List.{0} Int} {μ : Nat → Int},
      @Eq.{1} Nat m
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k) →
        @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word →
          @Eq.{1} Nat (@List.length.{0} Int as)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m) →
            @Eq.{1} Nat (@List.length.{0} Int bs)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m) →
              Light.Seg μ a as →
                Light.Seg μ b bs →
                  ThreeSum.Karatsuba.CoeffBound as (@Nat.cast.{0} Int instNatCastInt U) →
                    ThreeSum.Karatsuba.CoeffBound bs (@Nat.cast.{0} Int instNatCastInt U) →
                      @LE.le.{0} Nat instLENat
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                          work →
                        @LE.le.{0} Nat instLENat
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                            work →
                          @LE.le.{0} Nat instLENat
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) out
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)))
                              work →
                            @LE.le.{0} Nat instLENat
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) work
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)))
                                lim.space →
                              @LE.le.{0} Int Int.instLEInt
                                  (@Nat.cast.{0} Int instNatCastInt
                                    (ThreeSum.LightKaratsuba.wordBound
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)
                                      U))
                                  lim.word →
                                @LT.lt.{0} Nat instLTNat d lim.depth →
                                  (∀ (a' b' out' work' U' : Nat) (as' bs' : List.{0} Int) (μ' : Nat → Int),
                                      @Eq.{1} Nat (@List.length.{0} Int as') m →
                                        @Eq.{1} Nat (@List.length.{0} Int bs') m →
                                          Light.Seg μ' a' as' →
                                            Light.Seg μ' b' bs' →
                                              ThreeSum.Karatsuba.CoeffBound as' (@Nat.cast.{0} Int instNatCastInt U') →
                                                ThreeSum.Karatsuba.CoeffBound bs'
                                                    (@Nat.cast.{0} Int instNatCastInt U') →
                                                  @LE.le.{0} Nat instLENat
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        a' m)
                                                      work' →
                                                    @LE.le.{0} Nat instLENat
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          b' m)
                                                        work' →
                                                      @LE.le.{0} Nat instLENat
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat) out'
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                (instOfNatNat (nat_lit 2)))
                                                              m))
                                                          work' →
                                                        @LE.le.{0} Nat instLENat
                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                              (@instHAdd.{0} Nat instAddNat) work'
                                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                (@instHMul.{0} Nat instMulNat)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 8)
                                                                  (instOfNatNat (nat_lit 8)))
                                                                m))
                                                            lim.space →
                                                          @LE.le.{0} Int Int.instLEInt
                                                              (@Nat.cast.{0} Int instNatCastInt
                                                                (ThreeSum.LightKaratsuba.wordBound m U'))
                                                              lim.word →
                                                            Light.Meets lim P pSelf
                                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                (@instHAdd.{0} Nat instAddNat) d
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                  (instOfNatNat (nat_lit 1))))
                                                              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt m)
                                                                (@List.cons.{0} Int
                                                                  (@Nat.cast.{0} Int instNatCastInt a')
                                                                  (@List.cons.{0} Int
                                                                    (@Nat.cast.{0} Int instNatCastInt b')
                                                                    (@List.cons.{0} Int
                                                                      (@Nat.cast.{0} Int instNatCastInt out')
                                                                      (@List.cons.{0} Int
                                                                        (@Nat.cast.{0} Int instNatCastInt work')
                                                                        (@List.nil.{0} Int))))))
                                                              μ' (ThreeSum.LightKaratsuba.time k)
                                                              fun (x : Int) (μ'' : Nat → Int) =>
                                                              ThreeSum.LightKaratsuba.Result μ' out' m work' as' bs'
                                                                μ'') →
                                    Light.Ends lim P d (ThreeSum.LightKaratsuba.recurseBody pSelf pHalf pLinear pFill)
                                      {
                                        loc :=
                                          Light.frame
                                            (@List.cons.{0} Int
                                              (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
                                                (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))
                                                (@Nat.cast.{0} Int instNatCastInt m))
                                              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt a)
                                                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt b)
                                                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt out)
                                                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt work)
                                                      (@List.nil.{0} Int)))))),
                                        mem := μ }
                                      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                                        (ThreeSum.LightKaratsuba.time
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                                      fun (σ' : Light.State) =>
                                      ThreeSum.LightKaratsuba.Result μ out
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)
                                        work as bs σ'.mem := by
  exact @ThreeSum.LightKaratsuba.recurse_ends_sourceProof

#print axioms solution
