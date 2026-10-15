-- Prove2me | solution 1 for ThreeSum.LightModuloCounts.meets
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T16:37:34.54899+00:00
-- url     : https://prove2.me/submissions/389114c0-51bb-486c-87b4-56ae5c6c43ff

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
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
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
import Theorems.Thm_ThreeSum_Histograms_tripleMass_eq_histogram
import Theorems.Thm_ThreeSum_LightCapacity_meets
import Theorems.Thm_ThreeSum_LightCyclic_correlation_meets
import Theorems.Thm_ThreeSum_LightLookupSum_meets
import Theorems.Thm_ThreeSum_LightResidueHistogram_meets
import Theorems.Thm_ThreeSum_LightResidues_residues_ends


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


/-! # An exact global offset chosen by a cyclic correlation -/

namespace ThreeSum.Balancing

open Finset
open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]



theorem sum_correlation (F H : G → ℕ) :
    (∑ d, correlation F H d) = (∑ k, F k) * (∑ k, H k) := by
  unfold correlation
  rw [sum_comm]
  simp only [← mul_sum]
  have hshift (k : G) : (∑ d, H (k - d)) = ∑ d, H d := by
    exact Equiv.sum_comp (Equiv.subLeft k) H
  simp_rw [hshift]
  exact (sum_mul ..).symm

































end ThreeSum.Balancing

end

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
# Exact histogram and correlation counts

All weights are natural multiplicities.  In particular, raw A incidences and
repeated selected-map occurrences need not be deduplicated to use these
identities. The common offset is chosen from the actual key histograms.
-/

namespace ThreeSum.Histograms

open Finset
open scoped BigOperators

variable {ι τ ν G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]




theorem sum_histogram (I : Finset ι) (key : ι → G) (weight : ι → ℕ) :
    (∑ k, histogram I key weight k) = ∑ i ∈ I, weight i := by
  unfold histogram
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  simp



















































































end ThreeSum.Histograms

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























































































theorem residues_meets {pResidues pEmod : ℕ}
    (hres : P[pResidues]? = some (residuesBody pEmod))
    (hem : P[pEmod]? = some emodBody)
    {μ : ℕ → ℤ} {src dst n p work U : ℕ} {c : ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (hp : 0 < p) (hsrc : src + n ≤ work) (hdst : dst + n ≤ work)
    (hspace : work + (Nat.log 2 (U + 1) + 2) ≤ lim.space)
    (hsep : Apart src n dst n) (hc : |c| ≤ 1)
    (hword : (4 * U + 4 * p + 16 : ℤ) ≤ lim.word)
    (hvalues : ∀ i < n, |μ (src + i)| ≤ (U : ℤ)) :
    Meets lim P pResidues d [src, dst, n, p, work, c] μ (residuesTime n U)
      fun _ μ' =>
        (∀ i < n, μ' (dst + i) = (residue p c (μ (src + i)) : ℤ)) ∧
          KeptBut μ μ' work dst n := by
  exact Meets.of_body hres (residues_ends hem hw hd hp hsrc hdst hspace hsep hc hword hvalues)

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

theorem sum_signedHistogram {p : ℕ} [NeZero p]
    (c : ℤ) (values : ℕ → ℤ) (n : ℕ) :
    (∑ z : ZMod p, signedHistogram p c values n z) = n := by
  unfold signedHistogram
  rw [Histograms.sum_histogram]
  simp

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










theorem cast_add_eq_iff_dvd (p : ℕ) (a b c : ℤ) :
    (a : ZMod p) + (b : ZMod p) = (c : ZMod p) ↔ (p : ℤ) ∣ c-b-a := by
  have h := ZMod.intCast_eq_intCast_iff_dvd_sub (a+b) c p
  rw [show c-(a+b) = c-b-a by ring] at h
  simpa only [Int.cast_add] using h

theorem count_eq_tripleMass {p : ℕ} [NeZero p]
    (nA nB nC : ℕ) (a b c : ℕ → ℤ) :
    count p nA nB nC a b c =
      Histograms.tripleMass (range nA) (range nB) (range nC)
        (fun i => (a i : ZMod p)) (fun i => (b i : ZMod p))
        (fun i => (c i : ZMod p)) (fun _ => 1) (fun _ => 1) (fun _ => 1) := by
  unfold count Arithmetic.modCount triples difference Histograms.tripleMass
  simp only [sum_product, Arithmetic.dividesIndicator, one_mul]
  simp_rw [cast_add_eq_iff_dvd]

theorem count_eq_correlation {p : ℕ} [NeZero p]
    (nA nB nC : ℕ) (a b c : ℕ → ℤ) :
    count p nA nB nC a b c =
      ∑ i ∈ range nA, Balancing.correlation
        (signedHistogram p 1 c nC) (signedHistogram p 1 b nB) (a i : ZMod p) := by
  rw [count_eq_tripleMass, Histograms.tripleMass_eq_histogram]
  unfold LightResidueHistogram.signedHistogram
  simp only [one_mul]














theorem signedHistogram_congr {p c n} {a b : ℕ → ℤ}
    (hab : ∀ i < n, a i = b i) :
    signedHistogram p c a n = signedHistogram p c b n := by
  funext z
  unfold signedHistogram Histograms.histogram
  apply sum_congr rfl
  intro i hi
  simp only [hab i (mem_range.mp hi)]

theorem correlation_le {p : ℕ} [NeZero p]
    (nB nC : ℕ) (b c : ℕ → ℤ) (z : ZMod p) :
    Balancing.correlation (signedHistogram p 1 c nC) (signedHistogram p 1 b nB) z
      ≤ nB*nC := by
  have h := single_le_sum (f := Balancing.correlation
    (signedHistogram p 1 c nC) (signedHistogram p 1 b nB))
    (fun _ _ => Nat.zero_le _) (mem_univ z)
  rw [Balancing.sum_correlation, sum_signedHistogram, sum_signedHistogram] at h
  simpa only [Nat.mul_comm nC nB] using h

end ThreeSum.ModuloCounts

end

section


/-!
# A complete modular triple-counting procedure

Starting with three arrays of original signed integers and a positive modulus,
this fixed procedure computes its own power-of-two capacity, builds two padded
histograms, multiplies them with Karatsuba, folds the product into a correlation,
and looks up the residues of the A array. The result is exactly the modular
triple count used by the prime-score construction, including all multiplicities.
-/

namespace ThreeSum.LightModuloCounts

open Light ThreeSum.LightResidues ThreeSum.LightResidueHistogram
open ThreeSum.KaratsubaInterface ThreeSum.CyclicFold

variable {lim : Limits} {P : Program} {d : ℕ}




























theorem meets_sourceProof {pMain pCapacity pHist pCyclic pResidues pEmod
    pHistogram pMultiply pHalf pLinear pFill pLookup : ℕ}
    (hmain : P[pMain]? = some (body pCapacity pHist pCyclic pResidues pLookup))
    (hcap : P[pCapacity]? = some LightCapacity.body)
    (hhist : P[pHist]? = some (LightResidueHistogram.body pResidues pHistogram))
    (hres : P[pResidues]? = some (residuesBody pEmod))
    (hem : P[pEmod]? = some emodBody)
    (hcount : P[pHistogram]? = some (LightHistogram.histogramBody pFill))
    (hcyclic : P[pCyclic]? = some (LightCyclic.body pMultiply pLinear))
    (K : LightKaratsuba.Procs P pMultiply pHalf pLinear pFill)
    (hlookup : P[pLookup]? = some LightLookupSum.body)
    {μ : ℕ → ℤ} {a b c nA nB nC p N free U : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hp : 0 < p)
    (ha : a+nA ≤ free) (hb : b+nB ≤ free) (hc : c+nC ≤ free)
    (hnA : nA ≤ N) (hnB : nB ≤ N) (hnC : nC ≤ N)
    (hspace : space free p N U ≤ lim.space)
    (hword : (word p N U : ℤ) ≤ lim.word)
    (hd : d + Nat.clog 2 p + 3 ≤ lim.depth)
    (hA : ∀ i < nA, |μ (a+i)| ≤ (U : ℤ))
    (hB : ∀ i < nB, |μ (b+i)| ≤ (U : ℤ))
    (hC : ∀ i < nC, |μ (c+i)| ≤ (U : ℤ)) :
    Meets lim P pMain d [a,b,c,nA,nB,nC,p,N,free] μ (time p nA nB nC U)
      fun r μ' =>
        r = (ModuloCounts.count p nA nB nC
          (fun i => μ (a+i)) (fun i => μ (b+i)) (fun i => μ (c+i)) : ℤ) ∧
          Kept μ μ' free := by
  haveI : NeZero p := ⟨hp.ne'⟩
  let q := capacity p
  have hq : 0 < q := Nat.pow_pos (by decide)
  have hpq : p ≤ q := le_capacity p
  have hspace' : free+13*q+N+Nat.log 2 (U+1)+2 ≤ lim.space := hspace
  have hkw : (LightKaratsuba.wordBound q N : ℤ) ≤ lim.word := by
    have hh : LightKaratsuba.wordBound q N ≤ word p N U := by
      dsimp [word, q]
      omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hew : (4*U+4*p+16 : ℤ) ≤ lim.word := by
    have hh : 4*U+4*p+16 ≤ word p N U := by unfold word; omega
    have hhZ := (Int.ofNat_le.mpr hh).trans hword
    exact_mod_cast hhZ
  have hcw : ((2*p+1 : ℕ) : ℤ) ≤ lim.word := by
    push_cast
    omega
  have hsumword : ((nA*(nB*nC) : ℕ) : ℤ) ≤ lim.word := by
    have hprod : nA*(nB*nC) ≤ N^3 := by
      calc
        _ ≤ N*(N*N) := Nat.mul_le_mul hnA (Nat.mul_le_mul hnB hnC)
        _ = _ := by ring
    have hh : N^3 ≤ word p N U := by unfold word; omega
    exact (Int.ofNat_le.mpr (hprod.trans hh)).trans hword
  let F := signedHistogram p 1 (fun i => μ (c+i)) nC
  let H := signedHistogram p 1 (fun i => μ (b+i)) nB
  have hHneg : signedHistogram p (-1) (fun i => μ (b+i)) nB = (fun z => H (-z)) := by
    funext z
    exact signedHistogram_neg p _ _ z
  have hFbound : Karatsuba.CoeffBound (vector p F) (N : ℤ) := by
    have hh := padded_histogram_bound (p := p) 1 (fun i => μ (c+i)) nC 0
    simp only [padTo, Nat.zero_sub, List.replicate_zero, List.append_nil] at hh
    intro i
    exact (hh i).trans (by exact_mod_cast hnC)
  have hHbound : Karatsuba.CoeffBound (vector p (fun z => H (-z))) (N : ℤ) := by
    have hh := padded_histogram_bound (p := p) (-1) (fun i => μ (b+i)) nB 0
    simp only [padTo, Nat.zero_sub, List.replicate_zero, List.append_nil] at hh
    rw [hHneg] at hh
    intro i
    exact (hh i).trans (Int.ofNat_le.mpr hnB)
  apply Meets.of_body hmain
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
          Light.Ends.callToThen ((LightCapacity.meets hcap μ hp hcw) _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen (LightCapacity.meets hcap μ hp hcw) ?_ ?_ ?_ ?_);
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
            ((LightResidueHistogram.meets (d := d + 1) (src := b) (dst :=
                free + 2 * q) (codes := free + 5 * q) (work := free + 5 * q + N)
                (cap := q) (c := -1) hhist hres hem hcount K.fill hw (by omega) hp
                hpq (by omega) (by omega) (by omega) (by omega) (by norm_num) hew
                hB)
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (LightResidueHistogram.meets (d := d + 1) (src := b) (dst :=
              free + 2 * q) (codes := free + 5 * q) (work := free + 5 * q + N)
              (cap := q) (c := -1) hhist hres hem hcount K.fill hw (by omega) hp
              hpq (by omega) (by omega) (by omega) (by omega) (by norm_num) hew
              hB)
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
        ((rintro _ μ₁ ⟨hBseg, hkeep₁⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  rw [hHneg] at hBseg
  have hCread (i : ℕ) (hi : i < nC) : μ₁ (c+i) = μ (c+i) :=
    hkeep₁ _ ⟨by omega, by left; omega⟩
  have hC₁ : ∀ i < nC, |μ₁ (c+i)| ≤ (U : ℤ) := by
    intro i hi
    rw [hCread i hi]
    exact hC i hi
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
            ((LightResidueHistogram.meets (d := d + 1) (src := c) (dst :=
                free + q) (codes := free + 5 * q) (work := free + 5 * q + N)
                (cap := q) (c := 1) hhist hres hem hcount K.fill hw (by omega) hp
                hpq (by omega) (by omega) (by omega) (by omega) (by norm_num) hew
                hC₁)
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (LightResidueHistogram.meets (d := d + 1) (src := c) (dst := free + q)
              (codes := free + 5 * q) (work := free + 5 * q + N) (cap := q) (c :=
              1) hhist hres hem hcount K.fill hw (by omega) hp hpq (by omega)
              (by omega) (by omega) (by omega) (by norm_num) hew hC₁)
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
        ((rintro _ μ₂ ⟨hCseg, hkeep₂⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  have hCeq := ModuloCounts.signedHistogram_congr (p := p) (c := 1) hCread
  rw [hCeq] at hCseg
  have hBseg₂ : Seg μ₂ (free+2*q) (padTo q (vector p (fun z => H (-z)))) := by
    intro i hi
    have hlen : (padTo q (vector p (fun z => H (-z)))).length = q :=
      padTo_length _ _ (by rw [vector_length]; exact hpq)
    have hiq : i < q := by omega
    rw [hkeep₂ _ ⟨by omega, by right; omega⟩]
    exact hBseg i hi
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
            ((LightCyclic.correlation_meets (d := d + 1) (k := Nat.clog 2 p) (a :=
                free + q) (b := free + 2 * q) (prod := free + 3 * q) (dst := free)
                (work := free + 5 * q + N) hcyclic K F H hw hpq hCseg hBseg₂
                hFbound hHbound
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
            (LightCyclic.correlation_meets (d := d + 1) (k := Nat.clog 2 p) (a :=
              free + q) (b := free + 2 * q) (prod := free + 3 * q) (dst := free)
              (work := free + 5 * q + N) hcyclic K F H hw hpq hCseg hBseg₂ hFbound
              hHbound (by (change free + q + q ≤ free + 5 * q + N); (omega))
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
        ((rintro _ μ₃ ⟨hcorr, hkeep₃⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  have hkeepOriginal (i : ℕ) (hi : i < free) : μ₃ i = μ i := by
    rw [hkeep₃ i (by omega) (by left; omega) (by left; omega)]
    exact (hkeep₂ i ⟨by omega, by left; omega⟩).trans
      (hkeep₁ i ⟨by omega, by left; omega⟩)
  have hAread (i : ℕ) (hi : i < nA) : μ₃ (a+i) = μ (a+i) :=
    hkeepOriginal _ (by omega)
  have hA₃ : ∀ i < nA, |μ₃ (a+i)| ≤ (U : ℤ) := by
    intro i hi
    rw [hAread i hi]
    exact hA i hi
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
            ((residues_meets (d := d + 1) (src := a) (dst := free + 5 * q)
                (work := free + 5 * q + N) (c := 1) hres hem hw (by omega) hp
                (by omega) (by omega) (by omega) (by (left); (omega))
                (by norm_num) hew hA₃)
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (residues_meets (d := d + 1) (src := a) (dst := free + 5 * q) (work :=
              free + 5 * q + N) (c := 1) hres hem hw (by omega) hp (by omega)
              (by omega) (by omega) (by (left); (omega)) (by norm_num) hew hA₃)
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
        ((rintro _ μ₄ ⟨hkeys, hkeep₄⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  have hkeys₄ (i : ℕ) (hi : i < nA) :
      μ₄ (free+5*q+i) = (residue p 1 (μ (a+i)) : ℤ) := by
    rw [hkeys i hi, hAread i hi]
  have hcorr₄ (r : ℕ) (hr : r < p) :
      μ₄ (free+r) = (Balancing.correlation F H (r : ZMod p) : ℤ) := by
    rw [hkeep₄ _ ⟨by omega, by left; omega⟩, hcorr r hr]
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
            ((LightLookupSum.meets (d := d + 1) (keys := free + 5 * q) (table :=
                free) (n := nA) (p := p) (B := nB * nC) hlookup
                (fun i => residue p 1 (μ (a + i)))
                (fun r => Balancing.correlation F H (r : ZMod p)) hw (by omega)
                (by omega) hkeys₄ (fun i hi => residue_lt hp 1 (μ (a + i))) hcorr₄
                (fun r hr => ModuloCounts.correlation_le nB nC _ _ _) hsumword)
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (LightLookupSum.meets (d := d + 1) (keys := free + 5 * q) (table :=
              free) (n := nA) (p := p) (B := nB * nC) hlookup
              (fun i => residue p 1 (μ (a + i)))
              (fun r => Balancing.correlation F H (r : ZMod p)) hw (by omega)
              (by omega) hkeys₄ (fun i hi => residue_lt hp 1 (μ (a + i))) hcorr₄
              (fun r hr => ModuloCounts.correlation_le nB nC _ _ _) hsumword)
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
        ((rintro result μ₅ ⟨hresult, hmem₅⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  subst μ₅
  refine ⟨?_, ?_⟩
  · change result = _
    rw [hresult, ModuloCounts.count_eq_correlation]
    congr 1
    unfold LightLookupSum.prefixSum
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only
    rw [residue_zmod hp]
    simp only [one_mul]
    rfl
  · intro i hi
    exact (hkeep₄ i ⟨by omega, by left; omega⟩).trans (hkeepOriginal i hi)


























































































end ThreeSum.LightModuloCounts

end


theorem solution : ∀ {lim : Light.Limits} {P : Light.Program}
  {d pMain pCapacity pHist pCyclic pResidues pEmod pHistogram pMultiply pHalf pLinear pFill pLookup : Nat},
  @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pMain)
      (@Option.some.{0} Light.Stmt (ThreeSum.LightModuloCounts.body pCapacity pHist pCyclic pResidues pLookup)) →
    @Eq.{1} (Option.{0} Light.Stmt)
        (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
          (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
          (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pCapacity)
        (@Option.some.{0} Light.Stmt ThreeSum.LightCapacity.body) →
      @Eq.{1} (Option.{0} Light.Stmt)
          (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
            (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
            (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pHist)
          (@Option.some.{0} Light.Stmt (ThreeSum.LightResidueHistogram.body pResidues pHistogram)) →
        @Eq.{1} (Option.{0} Light.Stmt)
            (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
              (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
              (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pResidues)
            (@Option.some.{0} Light.Stmt (ThreeSum.LightResidues.residuesBody pEmod)) →
          @Eq.{1} (Option.{0} Light.Stmt)
              (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
                (fun (as : List.{0} Light.Stmt) (i : Nat) =>
                  @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
                (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pEmod)
              (@Option.some.{0} Light.Stmt Light.emodBody) →
            @Eq.{1} (Option.{0} Light.Stmt)
                (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
                  (fun (as : List.{0} Light.Stmt) (i : Nat) =>
                    @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
                  (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pHistogram)
                (@Option.some.{0} Light.Stmt (ThreeSum.LightHistogram.histogramBody pFill)) →
              @Eq.{1} (Option.{0} Light.Stmt)
                  (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
                    (fun (as : List.{0} Light.Stmt) (i : Nat) =>
                      @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
                    (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pCyclic)
                  (@Option.some.{0} Light.Stmt (ThreeSum.LightCyclic.body pMultiply pLinear)) →
                ThreeSum.LightKaratsuba.Procs P pMultiply pHalf pLinear pFill →
                  @Eq.{1} (Option.{0} Light.Stmt)
                      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
                        (fun (as : List.{0} Light.Stmt) (i : Nat) =>
                          @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
                        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pLookup)
                      (@Option.some.{0} Light.Stmt ThreeSum.LightLookupSum.body) →
                    ∀ {μ : Nat → Int} {a b c nA nB nC p N free U : Nat},
                      @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word →
                        @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) p →
                          @LE.le.{0} Nat instLENat
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a nA) free →
                            @LE.le.{0} Nat instLENat
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b nB) free →
                              @LE.le.{0} Nat instLENat
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c nC) free →
                                @LE.le.{0} Nat instLENat nA N →
                                  @LE.le.{0} Nat instLENat nB N →
                                    @LE.le.{0} Nat instLENat nC N →
                                      @LE.le.{0} Nat instLENat (ThreeSum.LightModuloCounts.space free p N U) lim.space →
                                        @LE.le.{0} Int Int.instLEInt
                                            (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightModuloCounts.word p N U))
                                            lim.word →
                                          @LE.le.{0} Nat instLENat
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
                                                  (Nat.clog
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) p))
                                                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                              lim.depth →
                                            (∀ (i : Nat),
                                                @LT.lt.{0} Nat instLTNat i nA →
                                                  @LE.le.{0} Int Int.instLEInt
                                                    (@abs.{0} Int instLatticeInt Int.instAddGroup
                                                      (μ
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          a i)))
                                                    (@Nat.cast.{0} Int instNatCastInt U)) →
                                              (∀ (i : Nat),
                                                  @LT.lt.{0} Nat instLTNat i nB →
                                                    @LE.le.{0} Int Int.instLEInt
                                                      (@abs.{0} Int instLatticeInt Int.instAddGroup
                                                        (μ
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat) b i)))
                                                      (@Nat.cast.{0} Int instNatCastInt U)) →
                                                (∀ (i : Nat),
                                                    @LT.lt.{0} Nat instLTNat i nC →
                                                      @LE.le.{0} Int Int.instLEInt
                                                        (@abs.{0} Int instLatticeInt Int.instAddGroup
                                                          (μ
                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                              (@instHAdd.{0} Nat instAddNat) c i)))
                                                        (@Nat.cast.{0} Int instNatCastInt U)) →
                                                  Light.Meets lim P pMain d
                                                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt a)
                                                      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt b)
                                                        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt c)
                                                          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt nA)
                                                            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt nB)
                                                              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt nC)
                                                                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt p)
                                                                  (@List.cons.{0} Int
                                                                    (@Nat.cast.{0} Int instNatCastInt N)
                                                                    (@List.cons.{0} Int
                                                                      (@Nat.cast.{0} Int instNatCastInt free)
                                                                      (@List.nil.{0} Int))))))))))
                                                    μ (ThreeSum.LightModuloCounts.time p nA nB nC U)
                                                    fun (r : Int) (μ' : Nat → Int) =>
                                                    And
                                                      (@Eq.{1} Int r
                                                        (@Nat.cast.{0} Int instNatCastInt
                                                          (ThreeSum.ModuloCounts.count p nA nB nC
                                                            (fun (i : Nat) =>
                                                              μ
                                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                  (@instHAdd.{0} Nat instAddNat) a i))
                                                            (fun (i : Nat) =>
                                                              μ
                                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                  (@instHAdd.{0} Nat instAddNat) b i))
                                                            fun (i : Nat) =>
                                                            μ
                                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                (@instHAdd.{0} Nat instAddNat) c i))))
                                                      (Light.Kept μ μ' free) := by
  exact @ThreeSum.LightModuloCounts.meets_sourceProof

#print axioms solution
