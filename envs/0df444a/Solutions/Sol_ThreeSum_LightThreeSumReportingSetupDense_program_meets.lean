-- Prove2me | solution 1 for ThreeSum.LightThreeSumReportingSetupDense.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T17:04:08.36167+00:00
-- url     : https://prove2.me/submissions/82f2a427-6713-48e0-8775-ddaa47ce26c1

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Aesop
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
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
import Definitions.Def_ThreeSum1962Source_Bundle12
import Definitions.Def_ThreeSum1962Source_Bundle13
import Definitions.Def_ThreeSum1962Source_Bundle14
import Definitions.Def_ThreeSum1962Source_Bundle16
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Ring.Nat
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Colex
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.Range
import Mathlib.Data.List.Sublists
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import Theorems.Thm_ThreeSum_BandCandidateRows_fromOwner_sound
import Theorems.Thm_ThreeSum_BandCandidateRows_mem_records_owner
import Theorems.Thm_ThreeSum_BandRawA_mem_aIndices_iff_owner
import Theorems.Thm_ThreeSum_BandRawA_mem_allProducts
import Theorems.Thm_ThreeSum_BandRawA_owner_weightedFalseCount
import Theorems.Thm_ThreeSum_EncodedColorParameterData_reads
import Theorems.Thm_ThreeSum_EncodedColorPipelineData_Stored_of_kept
import Theorems.Thm_ThreeSum_EncodedColorPipelineData_ordered
import Theorems.Thm_ThreeSum_LightDenseSetup_program_meets
import Theorems.Thm_ThreeSum_LightPrimePool_prefix_increasing


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async true
namespace Light
end Light
namespace ThreeSum.ArithmeticStageBounds
end ThreeSum.ArithmeticStageBounds
namespace ThreeSum.BandCandidateRows
end ThreeSum.BandCandidateRows
namespace ThreeSum.BandEnumeration
end ThreeSum.BandEnumeration
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition
namespace ThreeSum.BandRawA
end ThreeSum.BandRawA
namespace ThreeSum.BandScales
end ThreeSum.BandScales
namespace ThreeSum.BandWeightedScore
end ThreeSum.BandWeightedScore
namespace ThreeSum.ColorClassLists
end ThreeSum.ColorClassLists
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
namespace ThreeSum.EncodedColorLayout
end ThreeSum.EncodedColorLayout
namespace ThreeSum.EncodedColorNormalizedData
end ThreeSum.EncodedColorNormalizedData
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LightClassFilter
end ThreeSum.LightClassFilter
namespace ThreeSum.LightLocalCoverLayout
end ThreeSum.LightLocalCoverLayout
namespace ThreeSum.LightLocalCoverSchedule
end ThreeSum.LightLocalCoverSchedule
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.ThreeSumReportingSetupData
end ThreeSum.ThreeSumReportingSetupData
namespace ThreeSum.WeightedScore
end ThreeSum.WeightedScore
namespace ThreeSumApsp
end ThreeSumApsp

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

/-- A procedure of a program is a procedure, with the same number, of the program with more
procedures appended. -/
theorem getElem?_append_of_eq_some {P : Program} {p : ℕ} {body : Stmt} (h : P[p]? = some body)
    (R : Program) : (P ++ R)[p]? = some body := by
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 h).1]
  exact h














/-- A run stays a run when procedures are appended to the program. -/
theorem Exec.append {s : Stmt} {σ σ' : State} {c : ℕ} (h : Exec lim P d s σ σ' c) (R : Program) :
    Exec lim (P ++ R) d s σ σ' c := by
  induction h with
  | skip => exact .skip
  | set h => exact .set h
  | store h₁ h₂ h₃ => exact .store h₁ h₂ h₃
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | iteTrue h₁ h₂ _ ih => exact .iteTrue h₁ h₂ ih
  | iteFalse h₁ h₂ _ ih => exact .iteFalse h₁ h₂ ih
  | whileFalse h₁ h₂ => exact .whileFalse h₁ h₂
  | whileTrue h₁ h₂ _ _ ih₁ ih₂ => exact .whileTrue h₁ h₂ ih₁ ih₂
  | call h₁ h₂ h₃ _ ih => exact .call h₁ (getElem?_append_of_eq_some h₂ R) h₃ ih

/-! ## The rules -/






/-- More time and a weaker conclusion. -/
theorem Ends.mono {s σ T T' Q Q'} (h : Ends lim P d s σ T Q) (hT : T ≤ T')
    (hQ : ∀ σ', Q σ' → Q' σ') : Ends lim P d s σ T' Q' := by
  obtain ⟨σ', c, he, hc, hq⟩ := h
  exact ⟨σ', c, he, hc.trans hT, hQ _ hq⟩

/-- What is proved about a program holds for the program with more procedures appended. -/
theorem Ends.append {s σ T Q} (h : Ends lim P d s σ T Q) (R : Program) :
    Ends lim (P ++ R) d s σ T Q := by
  obtain ⟨σ', c, he, hc, hq⟩ := h
  exact ⟨σ', c, he.append R, hc, hq⟩

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
                                 | ((ring_nf); (omega)))) : Ends lim P d (s₁ ;; s₂) σ T Q :=
  Ends.seq T₁ (T - T₁) h (by omega)

/-- Brackets do not matter: a piece of several statements, followed by the rest of the program, is
run statement by statement. -/
theorem Ends.seqAssoc {σ : State} {T : ℕ} {s₁ s₂ s₃ : Stmt} {Q : State → Prop}
    (h : Ends lim P d (s₁ ;; (s₂ ;; s₃)) σ T Q) : Ends lim P d ((s₁ ;; s₂) ;; s₃) σ T Q := by
  obtain ⟨σ', _, he, hc, hq⟩ := h
  cases he with
  | seq he₁ he₂₃ =>
    cases he₂₃ with
    | seq he₂ he₃ => exact ⟨σ', _, .seq (.seq he₁ he₂) he₃, by omega, hq⟩

/-- A `skip` before the rest of the program takes no step. -/
theorem Ends.skipThen {σ : State} {T : ℕ} {s : Stmt} {Q : State → Prop} (h : Ends lim P d s σ T Q) :
    Ends lim P d (.skip ;; s) σ T Q :=
  Ends.seq 0 T (Ends.skip h) (by omega)

/-- A `skip` may be put behind a statement. -/
theorem Ends.skipLast {σ : State} {T : ℕ} {s : Stmt} {Q : State → Prop}
    (h : Ends lim P d (s ;; .skip) σ T Q) : Ends lim P d s σ T Q := by
  obtain ⟨σ', _, he, hc, hq⟩ := h
  cases he with
  | seq he₁ he₂ =>
    cases he₂
    exact ⟨σ', _, he₁, by omega, hq⟩

/-- A program that is defined as a sequence may be treated as the sequence. -/
theorem Ends.seqSelf {σ : State} {T : ℕ} {s₁ s₂ : Stmt} {Q : State → Prop}
    (h : Ends lim P d (s₁ ;; s₂) σ T Q) : Ends lim P d (s₁ ;; s₂) σ T Q :=
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
    Ends lim P d (.set x e ;; s) ⟨frame l, μ⟩ T Q :=
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

















/-- A specification holds for the program with more procedures appended. -/
theorem Meets.append (h : Meets lim P p d vals μ T R) (P' : Program) :
    Meets lim (P ++ P') p d vals μ T R := by
  obtain ⟨body, hp, he⟩ := h
  exact ⟨body, getElem?_append_of_eq_some hp P', he.append P'⟩

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
    Ends lim P d (.call p args x ;; s) ⟨frame l, μ⟩ T Q :=
  Ends.next _ (Ends.callTo hp h ha hd le_rfl) hT

end

end Light

end
end

section


/-!
# Regions of the memory, and the cells that a step leaves alone

A region is given by its first address `a` and its number `n` of cells.  `Inside a n b` says that
the cell `b` lies in it, `Outside a n b` that it does not, and `Apart a n a' n'` that two regions do
not meet.  `InOrder top [(a, n), (a', n'), …]` says that the listed regions lie one behind the other
and end at or below `top`.  All of these abbreviate linear inequalities.

`SameOn K μ μ'` says that the memory `μ'` agrees with `μ` on every cell that satisfies `K`.  It is
the one notion of "these cells are unchanged": a routine promises `SameOn K μ μ'` for the cells
`K` that it leaves alone.  (It is `Set.EqOn μ' μ {b | K b}`, stated with a predicate: the conditions
`K b` that occur are linear inequalities between addresses and are used as such.)  The usual choices
of `K` have names.

* `SameOutside μ μ' a n`: all cells outside one region; `SameOutside2` and `SameOutside3`: all cells
  outside two or three regions.
* `Kept μ μ' fr`: all cells below the free pointer `fr`.
* `KeptBut μ μ' fr out len`: all cells below `fr` outside the region of an output.

## How a fact is carried from one memory to a later one

A predicate `X` about a memory has one lemma of the name `X.keep` and of the form

  `theorem X.keep (h : X μ …) (hs : SameOn K μ μ' := by light_keep) : X μ' …`

where `K` describes the cells that `X` reads; `Seg.keep` is the model.  The argument `hs` has a
default proof.  So `h.keep`, with no argument, stands for "`h` still holds in the memory that is
asked for here".  The default proof `light_keep` uses every hypothesis of the form `SameOn _ ν ν'`
in the context, that is, the promises of the steps that were taken since `h` was obtained, and the
inequalities in the context that say where the regions lie.  In the proofs a promise is named when
the step is taken, as `same₂` in `rintro _ μ₂ ⟨sY, same₂⟩`.

`wrote μ dst f j` is the memory `μ` after a loop has written `f 0`, …, `f (j - 1)` to the cells from
`dst`.
-/

@[expose] public section

namespace Light

/-! ## Regions -/


















/-! ## Memories that agree on some cells -/























variable {K K' K₁ K₂ : ℕ → Prop} {μ μ' μ'' : ℕ → ℤ} {b : ℕ}























/-! ## Writing a region cell by cell -/

variable {dst j : ℕ} {f : ℕ → ℤ}














































/-! ## The tactics -/











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



























































































































/-- Reading a cell of a segment of natural numbers. -/
theorem SegN.read {l : List ℕ} (h : SegN μ a l) {i : ℕ} (hi : i < l.length) :
    μ (a + i) = ((l.getD i 0 : ℕ) : ℤ) := by
  rw [h i (by simpa using hi), List.getElem_map, List.getD_eq_getElem _ _ hi]




































































end Light

end
end

section


/-!
# Tactics for proofs about programs

A proof about a program follows the text of the program from top to bottom.  The goal is always
`Ends lim P d s ⟨frame l, μ⟩ T Q`, and the statement at the head of `s` decides what comes next:

| the head of the program | what to write                  | what it is told                       |
|-------------------------|--------------------------------|---------------------------------------|
| `x := e`                | `light_set z`                  | the value `z` of `e`                  |
| `mem[a] := e`           | `light_store b z`              | the address `b` and the value `z`     |
| `if c then … else …`    | `light_if h₁ h₂ : p`           | what the test says, and two names     |
| `x := p(args)`          | `light_call fact with …`       | what the procedure does (`Meets`)     |
| a piece with a lemma    | `light_piece fact with …`      | what the piece does (`Ends`)          |
| `skip`, nothing else    | `light_skip`                   |                                       |
| a loop, nothing else    | `refine Ends.forFrame …`       | invariant and number of rounds        |
| a loop, then more       | `refine Ends.next _ (…)`       | the loop's rule with `(hT := le_rfl)` |

Each tactic works whether or not more program follows, hands the steps that are left to the rest of
the program, and proves the side conditions (the expressions stay within the limits and have the
values that were given, the time suffices) by `light_side` and `light_time`.  What is left is the
goal about the rest of the program, or `Q` of the last state.  After `light_if` there are two goals,
first the one in which the test holds.  The patterns after `with` take apart, as those of `rintro`
do, what holds after the call or the piece.  Goals for holes `?_` in a `fact` come before the goal
about the rest of the program.

The side conditions are decided by linear arithmetic over the hypotheses in the context.
`light_facts H` puts the fields of a record `H` there.  What a side condition needs beyond that is
named after `using`: the content of a cell that is read, a definition to be unfolded, a running time
to be unfolded: `light_set K[j] using hkey`.

A program that is a definition is replaced by its text when a single statement is treated.  A
definition that stands at the head of a sequence stays closed: it is a piece, for `light_piece`.
-/

@[expose] public section

namespace Light

/-! ## Records -/



/-! ## One statement -/





























end Light

end
end

section


/-!
# The exact physical band-owner record order

There is one four-cell record for every owner-table cell, in BC, AB, AC
rectangle order. A zero flag is a lookup miss. Successful records retain
their physical owner slot even when several owners produce the same triple.
-/

namespace ThreeSum.BandCandidateRows

open BandEnumeration

set_option maxHeartbeats 1400000
set_option maxRecDepth 7000



















































theorem rect_length (m n : ℕ) (F : ℕ → ℕ → Record) : (rect m n F).length=m*n := by
  simp [rect,List.length_flatMap]

theorem records_length (A B C : Family) :
    (records A B C).length=LightBandEnumeration.count A.size B.size C.size := by
  simp only [records,List.length_append,rect_length,LightBandEnumeration.count]
  omega























































theorem make_flag (mode : Mode) (i j r : ℕ) :
    (make mode i j r).flag=0 ∨ (make mode i j r).flag=1 := by
  cases mode <;> simp only [make] <;> split_ifs <;> simp
























































































end ThreeSum.BandCandidateRows

end

section


/-! # List and memory interfaces for the exact candidate record array -/

namespace ThreeSum.BandCandidateRows

open Light BandEnumeration

set_option maxHeartbeats 1300000















theorem records_sound {A B C : Family} {r : Record}
    (hr : r ∈ records A B C) (hf : r.flag=1) :
    r.a < A.size ∧ r.b < B.size ∧ r.c < C.size ∧
      Bands.Relevant A.lower A.upper B.lower B.upper C.lower C.upper (r.a,r.b,r.c) := by
  obtain ⟨o,rfl⟩ := mem_records_owner hr
  exact fromOwner_sound A B C o hf

theorem records_flag {A B C : Family} {r : Record} (hr : r ∈ records A B C) :
    r.flag=0 ∨ r.flag=1 := by
  obtain ⟨o,rfl⟩ := mem_records_owner hr
  rcases o with ⟨j,k⟩ | ⟨i,j | k⟩ <;> exact make_flag _ _ _ _























































end ThreeSum.BandCandidateRows

end

section


/-!
# Consecutive bands of a strictly increasing array

The last band is truncated. Every input position belongs to its quotient
band, the bands are strictly separated, and each band has at most `g` entries.
The quotient in these specifications is realized by `LightBandPartition`.
-/

namespace ThreeSum.BandPartition





theorem size_le (n g : ℕ) : size n g ≤ n := by
  unfold size
  split_ifs with h
  · omega
  · have hdiv := Nat.div_le_self (n-1) g
    omega

theorem size_mono {n m g : ℕ} (h : n ≤ m) : size n g ≤ size m g := by
  by_cases hn : n = 0
  · simp [size,hn]
  · have hm : m ≠ 0 := by omega
    have hd := Nat.div_le_div_right (c := g) (show n-1 ≤ m-1 by omega)
    simp only [size,if_neg hn,if_neg hm]
    omega
























































































end ThreeSum.BandPartition

end

section


/-!
# A finite array minimum scan in the benchmark language

The selected index is a deterministic left-to-right minimum. Its value
can therefore instantiate the exact mean bound for offset balancing.
-/

namespace ThreeSum.LightMinimum

open Light





theorem least_lt (f : ℕ → ℤ) {n : ℕ} (hn : 0 < n) : least f n < n := by
  induction n with
  | zero => omega
  | succ n ih =>
      cases n with
      | zero => simp [least]
      | succ n =>
          have h := ih (by omega)
          unfold least
          split <;> omega


































variable {lim : Limits} {P : Program} {d : ℕ}





































end ThreeSum.LightMinimum

end

section


/-!
# Executing deterministic prime-score minimization

The same finite prime array supplies the candidate multipliers and the
auxiliary tests. The program streams exact scores at `q * primes i`, retaining
the first minimum. All weighted-score calls reuse one scratch region.
-/

namespace ThreeSum.LightPrimeMinimum

open Light WeightedScore

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

























theorem score_congr {primes : ℕ → ℕ} {s q nA nB nC : ℕ} {A A' B B' C C' : ℕ → ℤ}
    (ha : ∀ i < nA, A i = A' i) (hb : ∀ i < nB, B i = B' i)
    (hc : ∀ i < nC, C i = C' i) :
    score primes s q nA nB nC A B C = score primes s q nA nB nC A' B' C' := by
  unfold score Arithmetic.weightedFalseCount
  apply Finset.sum_congr rfl
  intro t ht
  simp only [ModuloCounts.triples, Finset.mem_product, Finset.mem_range] at ht
  simp only [ModuloCounts.difference, ha _ ht.1, hb _ ht.2.1, hc _ ht.2.2]
  rfl






































variable {lim : Limits} {P : Program} {d : ℕ}


















































































































































































































end ThreeSum.LightPrimeMinimum

end

section


/-!
# The aggregate weighted score of physical band-owner candidates

Each flagged owner contributes the score of its three actual truncated
bands. Owner multiplicities are retained. The contraction and initial bound
therefore apply to the same quadratic catalog that the program scans.
-/

namespace ThreeSum.BandWeightedScore

open BandCandidateRows Finset
open scoped BigOperators

set_option maxHeartbeats 1600000
set_option maxRecDepth 8000











theorem position_lt {n g a i : ℕ} (hi : i < length n g a) : a*g+i < n := by
  have hh := min_le_right g (n-a*g)
  unfold length at hi
  omega

































































theorem block_congr {primes : ℕ → ℕ} {s q nA nB nC g : ℕ}
    {A A' B B' C C' : ℕ → ℤ} (r : Record)
    (hA : ∀ i < nA, A i=A' i) (hB : ∀ i < nB, B i=B' i) (hC : ∀ i < nC, C i=C' i) :
    block primes s q nA nB nC g A B C r=block primes s q nA nB nC g A' B' C' r := by
  unfold block
  split_ifs
  · exact LightPrimeMinimum.score_congr
      (fun i hi => hA _ (position_lt hi)) (fun i hi => hB _ (position_lt hi))
      (fun i hi => hC _ (position_lt hi))
  · rfl

theorem score_congr {primes : ℕ → ℕ} {s q nA nB nC g : ℕ}
    {A A' B B' C C' : ℕ → ℤ} (rs : List Record)
    (hA : ∀ i < nA, A i=A' i) (hB : ∀ i < nB, B i=B' i) (hC : ∀ i < nC, C i=C' i) :
    score primes s q nA nB nC g A B C rs=score primes s q nA nB nC g A' B' C' rs := by
  unfold score partialScore
  exact sum_congr rfl fun i _ => block_congr (rs.getD i default) hA hB hC
































end ThreeSum.BandWeightedScore

end

section


/-!
# A common contracting modulus for the complete band-owner catalog

The same deterministic first-minimum rule is applied to the sum of every
flagged owner's score. These are joint choices for all bands, rather than
independent moduli whose contractions could not be combined.
-/

namespace ThreeSum.BandPrimeChoice

open BandCandidateRows BandWeightedScore Finset
open scoped BigOperators

set_option maxHeartbeats 1400000
set_option maxRecDepth 8000













theorem chosenIndex_lt (primes : ℕ → ℕ) {s q nA nB nC g : ℕ}
    (A B C : ℕ → ℤ) (rs : List Record) (hs : 0 < s) :
    chosenIndex primes s q nA nB nC g A B C rs < s := LightMinimum.least_lt _ hs
































theorem modulus_bounds (primes : ℕ → ℕ) {s nA nB nC g : ℕ}
    (A B C : ℕ → ℤ) (rs : List Record) (hs : 0 < s) (y Y r : ℕ)
    (hlo : ∀ i < s, y ≤ primes i) (hhi : ∀ i < s, primes i ≤ Y) :
    y^r ≤ modulus primes s nA nB nC g A B C rs r ∧
      modulus primes s nA nB nC g A B C rs r ≤ Y^r := by
  induction r with
  | zero => simp [modulus]
  | succ r ih =>
    have hidx := chosenIndex_lt (q := modulus primes s nA nB nC g A B C rs r)
      (nA := nA) (nB := nB) (nC := nC) (g := g) primes A B C rs hs
    constructor
    · simpa only [modulus,pow_succ,chosenPrime] using Nat.mul_le_mul ih.1 (hlo _ hidx)
    · simpa only [modulus,pow_succ,chosenPrime] using Nat.mul_le_mul ih.2 (hhi _ hidx)

theorem modulus_pos (primes : ℕ → ℕ) {s nA nB nC g : ℕ}
    (A B C : ℕ → ℤ) (rs : List Record) (hs : 0 < s)
    (hprime : ∀ i < s, Nat.Prime (primes i)) (r : ℕ) :
    0 < modulus primes s nA nB nC g A B C rs r := by
  have hh := (modulus_bounds (nA := nA) (nB := nB) (nC := nC) (g := g) primes A B C rs hs 1
    (Finset.sup (range s) primes) r
    (fun i hi => (hprime i hi).pos)
    (fun i hi => Finset.le_sup (mem_range.mpr hi))).1
  rw [one_pow] at hh
  omega

























































end ThreeSum.BandPrimeChoice

end

section


/-!
# Executing the candidate prime pool

This fixed program scans the integers in `(y,4*y]`, invokes the concrete
trial-division procedure, and writes every prime exactly once in increasing
order. The returned length and written array are the exact candidate pool
used by the contraction and auxiliary-weight theorems.
-/

namespace ThreeSum.LightPrimePool

open Light

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000






theorem prefix_length_le (y i : ℕ) : (scanned y i).length ≤ i := by
  induction i with
  | zero => simp [scanned]
  | succ i ih =>
      unfold scanned
      split
      · simp only [List.length_append,List.length_singleton]
        omega
      · omega






































theorem prefix_nodup (y i : ℕ) : (scanned y i).Nodup :=
  (prefix_increasing y i).imp (fun h => Nat.ne_of_lt h)






theorem values_nodup (y : ℕ) : (values y).Nodup := prefix_nodup y (3*y)
theorem size_le (y : ℕ) : size y ≤ 3*y := prefix_length_le y (3*y)























theorem prime_spec {y i : ℕ} (hi : i < size y) :
    Nat.Prime (prime y i) ∧ y < prime y i ∧ prime y i ≤ 4*y :=
  mem_values.mp (prime_mem hi)

theorem prime_injective {y i j : ℕ} (hi : i < size y) (hj : j < size y)
    (heq : prime y i = prime y j) : i = j :=
  (List.getD_inj hi hj (values_nodup y)).mp heq







theorem values_nonempty {y : ℕ} (hy : 0 < y) : values y ≠ [] := by
  obtain ⟨p,hp,hlo,hhi⟩ := Nat.exists_prime_lt_and_le_two_mul y hy.ne'
  have hmem : p ∈ values y := mem_values.mpr ⟨hp,hlo,by omega⟩
  intro heq
  simpa only [heq,List.not_mem_nil] using hmem

theorem size_pos {y : ℕ} (hy : 0 < y) : 0 < size y :=
  List.length_pos_iff.mpr (values_nonempty hy)


























































variable {lim : Limits} {P : Program} {d : ℕ}
























































































end ThreeSum.LightPrimePool

end

section


/-!
# Construct the prime pool and common contracting modulus from band records

The fixed host constructs the candidate prime array, then executes the
aggregate modulus chain on every owner record. The physical prime array and
every prefix modulus remain available to the encoder and reporting stages.
-/

namespace ThreeSum.LightBandPrimeConstruction

open Light BandCandidateRows

set_option maxHeartbeats 2200000
set_option maxRecDepth 10000





theorem modulus_bounds {y nA nB nC g : ℕ}
    (A B C : ℕ → ℤ) (rs : List Record) (levels : ℕ) (hy : 0 < y) :
    y^levels ≤ modulus y nA nB nC g A B C rs levels ∧
      modulus y nA nB nC g A B C rs levels ≤ (4*y)^levels :=
  BandPrimeChoice.modulus_bounds (LightPrimePool.prime y) A B C rs
    (LightPrimePool.size_pos hy) y (4*y) levels
    (fun i hi => (LightPrimePool.prime_spec hi).2.1.le)
    (fun i hi => (LightPrimePool.prime_spec hi).2.2)







































variable {lim : Limits} {d : ℕ} {μ : ℕ → ℤ}
    {a b c nA nB nC g recs y levels free maxMod U : ℕ}



















































































end ThreeSum.LightBandPrimeConstruction

end

section


/-!
# Each physical A incidence retains exactly its owner's B/C product

The products in this file are mathematical counting domains. The actual
catalog is still constructed by the verified quadratic owner loop and
linear band copies. Distinct owner products are disjoint because their
physical A incidence indices differ, even when their values coincide.
-/

namespace ThreeSum.BandRawA

open BandCandidateRows Finset
open scoped BigOperators

set_option maxHeartbeats 1900000
set_option maxRecDepth 8000



























































theorem mem_ownerProduct {nA nB nC g s : ℕ} {rs : List Record} {t : ℕ × ℕ × ℕ}
    (hs : s < rs.length) :
    t ∈ ownerProduct nA nB nC g rs s ↔
      t.1 < (items nA g rs).length ∧ (labelAt nA g rs t.1).owner=s ∧
        t.2.1 ∈ bandPositions nB g (rs.getD s default).b ∧
        t.2.2 ∈ bandPositions nC g (rs.getD s default).c := by
  simp only [ownerProduct,mem_product,mem_aIndices_iff_owner hs,and_assoc]

theorem ownerProduct_disjoint {nA nB nC g s t : ℕ} {rs : List Record}
    (hs : s < rs.length) (ht : t < rs.length) (hst : s ≠ t) :
    Disjoint (ownerProduct nA nB nC g rs s) (ownerProduct nA nB nC g rs t) := by
  apply disjoint_left.mpr
  intro x hx hy
  have hs' := (mem_ownerProduct hs).mp hx
  have ht' := (mem_ownerProduct ht).mp hy
  exact hst (hs'.2.1.symm.trans ht'.2.1)
















































theorem sum_allProducts (F : (ℕ × ℕ × ℕ) → ℕ) (nA nB nC g : ℕ)
    (rs : List Record) :
    (∑ t ∈ allProducts nA nB nC g rs, F t)=
      ∑ s ∈ range rs.length, ∑ t ∈ ownerProduct nA nB nC g rs s, F t := by
  unfold allProducts
  apply sum_biUnion
  intro s hs t ht hst
  exact ownerProduct_disjoint (mem_range.mp hs) (mem_range.mp ht) hst





























end ThreeSum.BandRawA

end

section


/-!
# The aggregate prime score is the exact physical incidence-product score

The executable A catalog supplies the first-coordinate values. Its owner
metadata supplies the B/C slices. Thus the mathematical score summed by
the actual prime selector counts this same domain with all multiplicities.
-/

namespace ThreeSum.BandRawA

open BandCandidateRows Finset
open scoped BigOperators

set_option maxHeartbeats 1900000
set_option maxRecDepth 8000







































theorem all_weightedFalseCount (primes : ℕ → ℕ) (aux q nA nB nC g : ℕ)
    (A B C : ℕ → ℤ) (rs : List Record) :
    Arithmetic.weightedFalseCount (allProducts nA nB nC g rs)
      (ModuloCounts.difference (valueAt nA g rs A) B C)
      (Auxiliary.moduli (WeightedScore.auxiliarySet primes aux)) q=
      BandWeightedScore.score primes aux q nA nB nC g A B C rs := by
  unfold Arithmetic.weightedFalseCount
  rw [sum_allProducts]
  unfold BandWeightedScore.score BandWeightedScore.partialScore
  apply sum_congr rfl
  intro s hs
  exact owner_weightedFalseCount primes aux q nA nB nC g A B C rs (mem_range.mp hs)














































end ThreeSum.BandRawA

end

section


/-!
# The actual integer block schedule

All four size parameters below are executable natural-number functions.
The finite bounds and limits concern these functions, including the even
rounding of the cube root and the divisibility constraints on the number
of blocks.  No asymptotic size premise is imposed on the schedule.
-/

namespace ThreeSum.Scales

open Filter Real
open scoped Topology

















































































noncomputable section








































































































































































































































































































theorem primeDepth_upper (R : ℕ → ℕ) {n : ℕ} (hR : 4 ≤ R n) :
    4 * (4 * primeWindow n) ^ primeDepth R n ≤ R n := by
  have hr : R n / 4 ≠ 0 := by omega
  have h := Nat.pow_log_le_self (4 * primeWindow n) hr
  have h4 := Nat.mul_le_mul_left 4 h
  have hd := Nat.div_mul_le_self (R n) 4
  simpa [primeDepth, Nat.mul_comm] using h4.trans (by simpa [Nat.mul_comm] using hd)












































































































































































































































































































































































































































































































































end

end ThreeSum.Scales

end

section


/-!
# Finite scale guarantees for the executed physical-owner modulus

These theorems instantiate the previously proved size-only mass bounds with
the common modulus actually constructed from the candidate record array.
The weighted count is over physical A incidences and their own B/C bands.
-/

namespace ThreeSum.BandPrimeScales

open BandCandidateRows Scales BandScales CostLedger

set_option maxHeartbeats 1600000
set_option maxRecDepth 9000



















theorem modulus_bounds (n nA nB nC : ℕ) (A B C : ℕ → ℤ) (rs : List Record) :
    primeWindow n^primeDepth radix n ≤ modulus n nA nB nC A B C rs ∧
      modulus n nA nB nC A B C rs ≤ (4*primeWindow n)^primeDepth radix n :=
  LightBandPrimeConstruction.modulus_bounds A B C rs _ (by have := primeWindow_ge_two n; omega)

/-- The integer guard used by the three-lift residue construction. -/
theorem modulus_guard {n nA nB nC : ℕ} (A B C : ℕ → ℤ) (rs : List Record)
    (hR : 4 ≤ radix n) : 4*modulus n nA nB nC A B C rs ≤ radix n :=
  (Nat.mul_le_mul_left 4 (modulus_bounds n nA nB nC A B C rs).2).trans
    (primeDepth_upper radix hR)





/-- Every candidate and auxiliary product fits the existing arithmetic cap. -/
theorem resource_modulus_bound {n : ℕ} (hR : 4 ≤ radix n) :
    (4*primeWindow n)^(primeDepth radix n+1) ≤ ArithmeticStageBounds.maxMod n := by
  have hh := primeDepth_upper radix hR
  have hp : (4*primeWindow n)^primeDepth radix n ≤ radix n := by omega
  rw [pow_succ]
  exact Nat.mul_le_mul hp (Nat.le_self_pow (by decide : (2 : ℕ) ≠ 0) _)







































































end ThreeSum.BandPrimeScales

end

section


/-!
# Bounded finite index types for the same physical owner products

The A type is the complete flattened incidence array; B and C are the
retained sorted arrays. Coordinate transport is injective and preserves
both each owner's product and its exact weighted collision score.
-/

namespace ThreeSum.BandRawA

open BandCandidateRows Finset
open scoped BigOperators

set_option maxHeartbeats 2000000
set_option maxRecDepth 8000




















theorem coordinates_injective {a b c : ℕ} :
    Function.Injective (@coordinates a b c) := by
  rintro ⟨i,j,k⟩ ⟨i',j',k'⟩ he
  simp only [coordinates,Prod.mk.injEq] at he
  exact Prod.ext (Fin.ext he.1) (Prod.ext (Fin.ext he.2.1) (Fin.ext he.2.2))

















@[simp] theorem mem_finiteAllProducts {nA nB nC g : ℕ} {rs : List Record}
    {t : Fin (items nA g rs).length × Fin nB × Fin nC} :
    t ∈ finiteAllProducts nA nB nC g rs ↔
      coordinates t ∈ allProducts nA nB nC g rs := by
  simp only [finiteAllProducts,mem_filter,mem_univ,true_and]













theorem allProducts_bounds {nA nB nC g : ℕ} {rs : List Record} {t : ℕ × ℕ × ℕ}
    (ht : t ∈ allProducts nA nB nC g rs) :
    t.1 < (items nA g rs).length ∧ t.2.1 < nB ∧ t.2.2 < nC := by
  obtain ⟨ha,hb,hc⟩ := mem_allProducts.mp ht
  exact ⟨ha,bandPositions_lt hb,bandPositions_lt hc⟩








theorem finite_lift {nA nB nC g : ℕ} {rs : List Record} {t : ℕ × ℕ × ℕ}
    (ht : t ∈ allProducts nA nB nC g rs) :
    ∃ u ∈ finiteAllProducts nA nB nC g rs, coordinates u=t := by
  obtain ⟨ha,hb,hc⟩ := allProducts_bounds ht
  refine ⟨(⟨t.1,ha⟩,⟨t.2.1,hb⟩,⟨t.2.2,hc⟩),?_,rfl⟩
  exact mem_finiteAllProducts.mpr ht
















theorem sum_finiteAllProducts (F : (ℕ × ℕ × ℕ) → ℕ) (nA nB nC g : ℕ)
    (rs : List Record) :
    (∑ u ∈ finiteAllProducts nA nB nC g rs, F (coordinates u))=
      ∑ t ∈ allProducts nA nB nC g rs, F t := by
  refine sum_bij (fun u _ => coordinates u) ?_ ?_ ?_ ?_
  · intro u hu
    exact mem_finiteAllProducts.mp hu
  · intro u hu v hv he
    exact coordinates_injective he
  · intro t ht
    obtain ⟨u,hu,he⟩ := finite_lift ht
    exact ⟨u,hu,he⟩
  · intro u hu
    rfl














theorem finiteAll_weightedFalseCount (primes : ℕ → ℕ) (aux q nA nB nC g : ℕ)
    (A B C : ℕ → ℤ) (rs : List Record) :
    Arithmetic.weightedFalseCount (finiteAllProducts nA nB nC g rs)
      (fun t => C t.2.2.val-B t.2.1.val-valueAt nA g rs A t.1.val)
      (Auxiliary.moduli (WeightedScore.auxiliarySet primes aux)) q=
      BandWeightedScore.score primes aux q nA nB nC g A B C rs := by
  rw [← all_weightedFalseCount primes aux q nA nB nC g A B C rs]
  unfold Arithmetic.weightedFalseCount
  exact sum_finiteAllProducts
    (fun t => if (q : ℤ) ∣ ModuloCounts.difference (valueAt nA g rs A) B C t then
      Arithmetic.missWeight (Auxiliary.moduli (WeightedScore.auxiliarySet primes aux))
        (ModuloCounts.difference (valueAt nA g rs A) B C t) else 0) nA nB nC g rs















end ThreeSum.BandRawA

end

section


/-!
# Stable extraction of one color class from the original signed array

The program reads stored colors and original values. It writes a length
header followed by exactly the selected values, optionally negated. Repeated
values are preserved; deduplication belongs to the later normalization pass.
-/

namespace ThreeSum.LightClassFilter

open Light

set_option maxHeartbeats 1200000












theorem items_length_le (x : ℕ → ℤ) (color : ℕ → ℕ) (want : ℕ) (scale : ℤ) (n : ℕ) :
    (items x color want scale n).length ≤ n := by
  simpa only [items,List.length_map,List.length_range] using
    List.length_filter_le (p := fun i => decide (color i = want)) (l := List.range n)

theorem mem_items (x : ℕ → ℤ) (color : ℕ → ℕ) (want : ℕ) (scale : ℤ) (n : ℕ) (z : ℤ) :
    z ∈ items x color want scale n ↔ ∃ i, i < n ∧ color i = want ∧ scale*x i = z := by
  simp [items,and_assoc]





















variable {lim : Limits} {P : Program} {d : ℕ}























































































end ThreeSum.LightClassFilter

end

section


/-!
# Exact original-position semantics of the constructed color-class lists

The machine keeps repeated values within a class and negates the third
class. The list membership witnesses are original positions. Any binary
width large enough for the indices suffices for the deterministic family.
-/

namespace ThreeSum.ColorClassLists

open LightClassFilter




































theorem length_classList_le {n W : ℕ} (p : Coloring.Parameter W) (x : Fin n → ℤ)
    (c : ℕ) (scale : ℤ) : (classList p x c scale).length ≤ n :=
  items_length_le ..



































































end ThreeSum.ColorClassLists

end

section


/-! # Retained common-prime metadata for one actual color execution -/

namespace ThreeSum.EncodedColorPrimeData

open Light













theorem Stored.heads_read {μ : ℕ → ℤ} {free M y : ℕ} {qs : ℕ → ℕ} (H : Stored μ free M y qs) :
    μ free=(qs (LightBandPrimeDepth.depth M y) : ℤ) ∧
    μ (free+1)=(LightBandPrimeDepth.depth M y : ℤ) ∧
    μ (free+2)=(nextFree free M y : ℤ) ∧
    μ (free+3)=(poolBase free : ℤ) ∧
    μ (free+4)=(LightPrimePool.size y : ℤ) ∧
    μ (free+5)=(prefixBase free y : ℤ) := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · simpa [values] using H.header.getD (i := 0) (by simp [values]) 0
  · simpa [values] using H.header.getD (i := 1) (by simp [values]) 0
  · simpa [values] using H.header.getD (i := 2) (by simp [values]) 0
  · simpa [values] using H.header.getD (i := 3) (by simp [values]) 0
  · simpa [values] using H.header.getD (i := 4) (by simp [values]) 0
  · simpa [values] using H.header.getD (i := 5) (by simp [values]) 0

















end ThreeSum.EncodedColorPrimeData

end

section


/-!
# Original input to normalized color bands

This fixed program computes index colors, writes the three class arrays and
their headers, then reads those headers into the existing normalization and
owner-table program. All buffers and resource bounds depend on the original
input length, rather than on externally supplied color-class lengths.
-/

namespace ThreeSum.LightColorBands

open Light ColorClassLists

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000













theorem class_bounded {n W U : ℕ} (p : Coloring.Parameter W) (x : Fin n → ℤ)
    (c : ℕ) (scale : ℤ) (hs : |scale| ≤ 1) (hx : ∀ i, |x i| ≤ (U : ℤ)) :
    ∀ z ∈ classList p x c scale, |z| ≤ (U : ℤ) := by
  intro z hz
  obtain ⟨i,hi,_,rfl⟩ :=
    (LightClassFilter.mem_items (value x) (LightColorIndex.color p) c scale n z).mp hz
  have hv : |value x i| ≤ (U : ℤ) := by
    simpa only [value,hi,dite_true] using hx ⟨i,hi⟩
  rw [abs_mul]
  calc
    |scale| * |value x i| ≤ 1 * (U : ℤ) :=
      mul_le_mul hs hv (abs_nonneg _) (by norm_num)
    _ = (U : ℤ) := one_mul _








variable {lim : Limits} {P : Program} {d : ℕ}

























































































































end ThreeSum.LightColorBands

end

section


/-! # One compact retained layout for a selected color -/

namespace ThreeSum.EncodedColorLayout





















theorem normalized_ends_before_count (free n g : ℕ) :
    av free n+n ≤ normalizedEnd free n g ∧ ae free n+2+2*n ≤ normalizedEnd free n g ∧
    bv free n+n ≤ normalizedEnd free n g ∧ be free n+2+2*n ≤ normalizedEnd free n g ∧
    cv free n+n ≤ normalizedEnd free n g ∧ ce free n+2+2*n ≤ normalizedEnd free n g ∧
    tables free n+ColorBandBounds.count n g ≤ normalizedEnd free n g ∧
    rec free n g+4*ColorBandBounds.count n g ≤ normalizedEnd free n g := by
  unfold normalizedEnd LightBandRawA.space LightBandRawA.positionBase LightBandRawA.ownerBase
    LightBandRawA.capacity vals rec tables ce cv be bv ae av
  omega





















theorem prime_le_cover (free n g M y : ℕ) : prime free n g+6 ≤ cover free n g M y := by
  unfold cover EncodedColorPrimeData.nextFree EncodedColorPrimeData.prefixBase EncodedColorPrimeData.poolBase
  omega

theorem normalized_ends_cover (free n g M y : ℕ) :
    av free n+n ≤ cover free n g M y ∧ ae free n+2+2*n ≤ cover free n g M y ∧
    bv free n+n ≤ cover free n g M y ∧ be free n+2+2*n ≤ cover free n g M y ∧
    cv free n+n ≤ cover free n g M y ∧ ce free n+2+2*n ≤ cover free n g M y ∧
    tables free n+ColorBandBounds.count n g ≤ cover free n g M y ∧
    rec free n g+4*ColorBandBounds.count n g ≤ cover free n g M y ∧
    LightBandRawA.space (vals free n g) (ColorBandBounds.count n g) g ≤ cover free n g M y := by
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩ := normalized_ends_before_count free n g
  have h := prime_le_cover free n g M y
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ normalizedEnd free n g ≤ _
  unfold prime at h
  omega

end ThreeSum.EncodedColorLayout

end

section


/-! # Concrete source inputs from the retained normalization and wanted outputs -/

namespace ThreeSum.SourceFiniteInputs

open Light GlobalEncoding LocalCoverBounds LightLocalCoverLayout LightLocalCoverSchedule






















theorem prepared_read {μ : ℕ → ℤ} {values endpoints g : ℕ} {hg : 0 < g}
    {original L : List ℤ} {hs : L.Pairwise (· < ·)}
    (H : LightBandPreprocessing.Represents μ values endpoints g hg original L hs) :
    ∀ j < L.length, μ (values+j)=L.getD j 0 := fun j hj => H.1.getD hj 0

theorem prepared_headers {μ : ℕ → ℤ} {values endpoints g : ℕ} {hg : 0 < g}
    {original L : List ℤ} {hs : L.Pairwise (· < ·)}
    (H : LightBandPreprocessing.Represents μ values endpoints g hg original L hs) :
    μ endpoints=(L.length : ℤ) ∧ μ (endpoints+1)=(BandPartition.size L.length g : ℤ) :=
  ⟨H.2.2.2.1,H.2.2.2.2.1⟩

theorem prepared_bound {μ : ℕ → ℤ} {values endpoints g U : ℕ} {hg : 0 < g}
    {original L : List ℤ} {hs : L.Pairwise (· < ·)}
    (H : LightBandPreprocessing.Represents μ values endpoints g hg original L hs)
    (hb : ∀ z ∈ original, |z| ≤ (U : ℤ)) :
    ∀ j < L.length, |L.getD j 0| ≤ (U : ℤ) := by
  intro j hj
  rw [List.getD_eq_getElem _ _ hj]
  exact hb _ ((H.2.2.1 _).mp (List.getElem_mem hj))


















end ThreeSum.SourceFiniteInputs

end

section


/-!
# The executed common-prime stage at the actual integer schedule

This interface consumes the physical records produced by the band catalog.
It derives every flag, band-start and candidate-count premise from that
catalog, computes the depth and pool, and returns the arithmetic guard and
the finite physical-domain false-mass bound at the actual execution cost.
-/

namespace ThreeSum.LightBandPrimeStage

open Light BandEnumeration BandCandidateRows Scales BandScales CostLedger

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000












theorem records_valid {A B C : Family} {nA nB nC g : ℕ}
    (hA : A.size=BandPartition.size nA g)
    (hB : B.size=BandPartition.size nB g)
    (hC : C.size=BandPartition.size nC g) (hg : 0 < g) :
    ∀ r ∈ records A B C, r.flag=1 → r.a*g ≤ nA ∧ r.b*g ≤ nB ∧ r.c*g ≤ nC := by
  intro r hr hf
  obtain ⟨ha,hb,hc,_⟩ := records_sound hr hf
  rw [hA] at ha
  rw [hB] at hb
  rw [hC] at hc
  exact ⟨(BandPartition.start_lt hg ha).le,(BandPartition.start_lt hg hb).le,
    (BandPartition.start_lt hg hc).le⟩













variable {lim : Limits} {d : ℕ} {μ : ℕ → ℤ}
    {a b c n nA nB nC k recs free : ℕ}































































end ThreeSum.LightBandPrimeStage

end

section


/-! # Actual finite budgets of the retained common-prime stage -/

namespace ThreeSum.EncodedColorPrimeCosts

open Light Scales BandScales CostLedger ArithmeticStageBounds
















theorem count_mono {nA nB nC nA' nB' nC' g : ℕ} (ha : nA ≤ nA') (hb : nB ≤ nB') (hc : nC ≤ nC') :
    LightEncodedColorPrime.count nA nB nC g ≤ LightEncodedColorPrime.count nA' nB' nC' g := by
  have a := BandPartition.size_mono (g := g) ha
  have b := BandPartition.size_mono (g := g) hb
  have c := BandPartition.size_mono (g := g) hc
  unfold LightEncodedColorPrime.count
  exact Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul b c) (Nat.mul_le_mul a b)) (Nat.mul_le_mul a c)






































theorem moduli_pos {A B C : List ℤ} {g y : ℕ} {hg : 0 < g}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (hy : 0 < y) (i : ℕ) : 0 < LightEncodedColorPrime.moduli A B C g hg hsA hsB hsC y i :=
  BandPrimeChoice.modulus_pos (LightPrimePool.prime y)
    (fun j => A.getD j 0) (fun j => B.getD j 0) (fun j => C.getD j 0)
    (BandRawA.sortedRecords A B C g hg hsA hsB hsC) (LightPrimePool.size_pos hy)
    (fun j hj => (LightPrimePool.prime_spec hj).1) i

theorem scheduled_modulus_eq (n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) :
    LightEncodedColorPrime.moduli A B C (bandSize n) (bandSize_pos n) hsA hsB hsC (primeWindow n)
      (LightBandPrimeDepth.depth (radix n) (primeWindow n))=
      BandPrimeScales.modulus n A.length B.length C.length
        (fun j => A.getD j 0) (fun j => B.getD j 0) (fun j => C.getD j 0)
        (BandRawA.sortedRecords A B C (bandSize n) (bandSize_pos n) hsA hsB hsC) := rfl

theorem scheduled_modulus_guard {n : ℕ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (hR : 4 ≤ radix n) :
    4*LightEncodedColorPrime.moduli A B C (bandSize n) (bandSize_pos n) hsA hsB hsC (primeWindow n)
      (LightBandPrimeDepth.depth (radix n) (primeWindow n)) ≤ radix n := by
  rw [scheduled_modulus_eq]
  exact BandPrimeScales.modulus_guard _ _ _ _ hR

end ThreeSum.EncodedColorPrimeCosts

end

section


/-! # Retained normalized pointers and the actual incidence-count cell -/

namespace ThreeSum.EncodedColorNormalizedData

open Light Scales BandScales ColorClassLists BandRawA EncodedColorLayout
















theorem records_length_le {A B C : List ℤ} {g n : ℕ} {hg : 0 < g}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (ha : A.length ≤ n) (hb : B.length ≤ n) (hc : C.length ≤ n) :
    (sortedRecords A B C g hg hsA hsB hsC).length ≤ ColorBandBounds.count n g := by
  have h := EncodedColorPrimeCosts.count_mono (g := g) ha hb hc
  have hright : LightEncodedColorPrime.count n n n g=ColorBandBounds.count n g := by
    unfold LightEncodedColorPrime.count ColorBandBounds.count
    ring
  rw [hright] at h
  simp only [sortedRecords, BandCandidateRows.records_length]
  exact h














theorem heads_read {μ : ℕ → ℤ} {free n g : ℕ} (H : Seg μ free (normalizedHeads free n g)) :
    μ free=(av free n : ℤ) ∧ μ (free+1)=(ae free n : ℤ) ∧
    μ (free+2)=(bv free n : ℤ) ∧ μ (free+3)=(be free n : ℤ) ∧
    μ (free+4)=(cv free n : ℤ) ∧ μ (free+5)=(ce free n : ℤ) ∧
    μ (free+6)=(rec free n g : ℤ) ∧ μ (free+7)=(vals free n g : ℤ) := by
  have h (i : ℕ) (hi : i < 8) := H.getD (i := i) (by simpa [normalizedHeads] using hi) 0
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa [normalizedHeads] using h 0 (by omega)
  · simpa [normalizedHeads] using h 1 (by omega)
  · simpa [normalizedHeads] using h 2 (by omega)
  · simpa [normalizedHeads] using h 3 (by omega)
  · simpa [normalizedHeads] using h 4 (by omega)
  · simpa [normalizedHeads] using h 5 (by omega)
  · simpa [normalizedHeads] using h 6 (by omega)
  · simpa [normalizedHeads] using h 7 (by omega)

end ThreeSum.EncodedColorNormalizedData

end

section


/-! # The same normalized finite witnesses and their actually selected prime -/

namespace ThreeSum.EncodedColorPrimeReadyData

open Light Scales BandScales ColorClassLists EncodedColorLayout EncodedColorNormalizedData





















theorem selected_pos {n : ℕ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)} :
    0 < selected n A B C hsA hsB hsC :=
  EncodedColorPrimeCosts.moduli_pos (lt_of_lt_of_le (by decide : 0 < 2) (primeWindow_ge_two n)) _

theorem selected_guard {n : ℕ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (hR : 4 ≤ radix n) : 4*selected n A B C hsA hsB hsC ≤ radix n :=
  EncodedColorPrimeCosts.scheduled_modulus_guard hR

end ThreeSum.EncodedColorPrimeReadyData

end

section


/-! # Keep the complete selected-color payload while later stages extend memory -/

namespace ThreeSum.EncodedColorPipelineData

open Light Scales BandScales ColorClassLists EncodedColorNormalizedData

set_option maxHeartbeats 1400000
set_option maxRecDepth 10000

theorem Stored.heads_read {μ : ℕ → ℤ} {free n : ℕ} {color : Coloring.Parameter (inputBits n+1)}
    {x : Fin n → ℤ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (H : Stored μ free n color x A B C hsA hsB hsC) :
    let out := finish free n A B C hsA hsB hsC
    μ out=(EncodedColorLayout.prime free n (bandSize n) : ℤ) ∧
    μ (out+1)=(coverBase free n : ℤ) ∧
    μ (out+2)=(wantedHeader free n (incidences n A B C hsA hsB hsC).length : ℤ) ∧
    μ (out+3)=(controls free n A B C hsA hsB hsC : ℤ) ∧
    μ (out+4)=(bankHeader free n A B C hsA hsB hsC : ℤ) ∧
    μ (out+5)=(out+8 : ℕ) ∧
    μ (out+6)=((incidences n A B C hsA hsB hsC).length : ℤ) ∧
    μ (out+7)=(EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC : ℤ) := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa [values,LightEncodedColorResult.values] using H.heads.getD (i := 0) (by simp [values,LightEncodedColorResult.values]) 0
  · simpa [values,LightEncodedColorResult.values] using H.heads.getD (i := 1) (by simp [values,LightEncodedColorResult.values]) 0
  · simpa [values,LightEncodedColorResult.values] using H.heads.getD (i := 2) (by simp [values,LightEncodedColorResult.values]) 0
  · simpa [values,LightEncodedColorResult.values] using H.heads.getD (i := 3) (by simp [values,LightEncodedColorResult.values]) 0
  · simpa [values,LightEncodedColorResult.values] using H.heads.getD (i := 4) (by simp [values,LightEncodedColorResult.values]) 0
  · simpa [values,LightEncodedColorResult.values] using H.heads.getD (i := 5) (by simp [values,LightEncodedColorResult.values]) 0
  · simpa [values,LightEncodedColorResult.values] using H.heads.getD (i := 6) (by simp [values,LightEncodedColorResult.values]) 0
  · simpa [values,LightEncodedColorResult.values] using H.heads.getD (i := 7) (by simp [values,LightEncodedColorResult.values]) 0














































end ThreeSum.EncodedColorPipelineData

end

section


/-! # Uniform budgets for wanted records followed by the shared source banks -/

namespace ThreeSum.EncodedColorStageCosts

open Scales BandScales ArithmeticStageBounds









































































theorem selected_le_maxMod {n : ℕ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (hR : 4 ≤ radix n) : EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC ≤ maxMod n := by
  have hp := EncodedColorPrimeReadyData.selected_guard (A := A) (B := B) (C := C)
    (hsA := hsA) (hsB := hsB) (hsC := hsC) hR
  have hy := primeWindow_ge_two n
  have hm : radix n ≤ maxMod n := by
    unfold maxMod
    exact Nat.le_mul_of_pos_right _ (by positivity)
  omega

end ThreeSum.EncodedColorStageCosts

end

section


/-!
# Construct the dense-stop threshold from actual cover and source records

The host computes the representation cap, recomputes the exact aggregate
weighted score at the selected common modulus, multiplies the two, and
initializes the running counter. The four retained cells are counter,
threshold, representation cap and weighted score. Scratch starts after them.
-/

namespace ThreeSum.LightDenseSetup

open Light GlobalEncoding BandCandidateRows

set_option maxHeartbeats 2200000
set_option maxRecDepth 10000




































theorem falseScore_eq (primes : ℕ → ℕ) (s q nA nB nC g : ℕ)
    (A B C : ℕ → ℤ) (rs : List Record) :
    falseScore primes s q nA nB nC g A B C rs=
      BandWeightedScore.score primes s q nA nB nC g A B C rs :=
  BandRawA.finiteAll_weightedFalseCount primes s q nA nB nC g A B C rs

variable {lim : Limits} {d : ℕ} {μ : ℕ → ℤ}
    {a b c nA nB nC g recs q aux s cover free maxMod U h J : ℕ}




























































































end ThreeSum.LightDenseSetup

end

section


/-!
# Actual encoding-output masses fit the uniform reporting budgets

Both inequalities come from the retained pipeline payload. The wanted
count includes all physical A occurrences and all three lifts; the false
score uses the very common modulus selected from the original normalized
arrays. No input-dependent counting or prime-quality premise is assumed.
The explicit numerical divisor premise is discharged eventually, uniformly
before the input arrays are quantified.
-/

namespace ThreeSum.ThreeSumColorBudgets

open Light Scales BandScales CostLedger GlobalEncoding LocalCoverBounds
open ColorClassLists EncodedColorNormalizedData

set_option maxHeartbeats 2200000
set_option maxRecDepth 12000


















variable {μ : ℕ → ℤ} {free n : ℕ}
    {color : Coloring.Parameter (inputBits n+1)} {x : Fin n → ℤ}
    {A B C : List ℤ} {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}

theorem normalized_lengths (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC) :
    A.length ≤ n ∧ B.length ≤ n ∧ C.length ≤ n :=
  ⟨H.normalized.2.1.2.1.trans (length_classList_le color x 0 1),
    H.normalized.2.2.1.2.1.trans (length_classList_le color x 1 1),
    H.normalized.2.2.2.1.2.1.trans (length_classList_le color x 2 (-1))⟩

theorem normalized_values {U : ℕ}
    (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (hx : ∀ i, |x i| ≤ (U : ℤ)) :
    (∀ j < A.length, |A.getD j 0| ≤ (U : ℤ)) ∧
      (∀ j < B.length, |B.getD j 0| ≤ (U : ℤ)) ∧
      (∀ j < C.length, |C.getD j 0| ≤ (U : ℤ)) :=
  ⟨SourceFiniteInputs.prepared_bound H.normalized.2.1
      (LightColorBands.class_bounded color x 0 1 (by norm_num) hx),
    SourceFiniteInputs.prepared_bound H.normalized.2.2.1
      (LightColorBands.class_bounded color x 1 1 (by norm_num) hx),
    SourceFiniteInputs.prepared_bound H.normalized.2.2.2.1
      (LightColorBands.class_bounded color x 2 (-1) (by norm_num) hx)⟩













































































open Filter













end ThreeSum.ThreeSumColorBudgets

end

section


/-! # Exact retained addresses for reporting one encoded original color -/

namespace ThreeSum.ThreeSumReportingSetupData

open Light Scales BandScales EncodedColorNormalizedData

attribute [local instance] _root_.ThreeSum.ThreeSumReportingSetupData.instNeZeroNatRadix






































theorem prefix_le_report (free n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) :
    free+8 ≤ reportBase free n A B C hsA hsB hsC ∧
    EncodedColorPipelineData.coverBase free n ≤ reportBase free n A B C hsA hsB hsC := by
  obtain ⟨_,hf,hc,_,hs,_⟩ := EncodedColorPipelineData.ordered free n A B C hsA hsB hsC
  unfold reportBase
  omega

theorem cover_end_le_report (free n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) :
    LightCoverKeyData.keyEnd (EncodedColorPipelineData.coverBase free n)
      (microHalf (inputBits n)) (blockCount (inputBits n)) ≤ reportBase free n A B C hsA hsB hsC := by
  obtain ⟨_,_,_,hw,hs,_⟩ := EncodedColorPipelineData.ordered free n A B C hsA hsB hsC
  have he : EncodedColorPipelineData.wantedHeader free n (incidences n A B C hsA hsB hsC).length=
      LightCoverKeyData.keyEnd (EncodedColorPipelineData.coverBase free n)
        (microHalf (inputBits n)) (blockCount (inputBits n))+3*(incidences n A B C hsA hsB hsC).length := rfl
  unfold reportBase
  omega

theorem pool_end_le_report (free n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) :
    EncodedColorPrimeData.poolBase (EncodedColorLayout.prime free n (bandSize n))+
      LightPrimePool.size (primeWindow n) ≤ reportBase free n A B C hsA hsB hsC := by
  have hp := (prefix_le_report free n A B C hsA hsB hsC).2
  have hs := LightPrimePool.size_le (primeWindow n)
  unfold EncodedColorPipelineData.coverBase EncodedColorLayout.cover
    EncodedColorPrimeData.nextFree EncodedColorPrimeData.prefixBase at hp
  omega

end ThreeSum.ThreeSumReportingSetupData

end

section


/-! # Initialize the actual dense counter using the retained original arrays -/

namespace ThreeSum.LightThreeSumReportingSetupDense

open Light Scales BandScales CostLedger ArithmeticStageBounds ThreeSumReportingSetupData
open BandPartition BandCandidateRows BandRawA

set_option maxHeartbeats 2600000
set_option maxRecDepth 16000

local instance (n : ℕ) : NeZero (radix n) := ⟨Nat.ne_of_gt (radix_pos n)⟩








































theorem dense_word_le {n nA nB nC R U : ℕ}
    (hA : nA ≤ n) (hB : nB ≤ n) (hC : nC ≤ n) (hR : R ≤ ColorBandBounds.count n (bandSize n)) :
    LightDenseSetup.word (maxMod n) nA nB nC (bandSize n) R
      (LightPrimePool.size (primeWindow n)) U (microHalf (inputBits n)) (blockCount (inputBits n)) ≤ word n U := by
  apply le_trans (b := LightDenseSetup.word (maxMod n) n n n (bandSize n)
    (ColorBandBounds.count n (bandSize n)) (LightPrimePool.size (primeWindow n)) U
    (microHalf (inputBits n)) (blockCount (inputBits n)))
  · unfold LightDenseSetup.word LightBandWeightedScore.word LightBandWeightedScoreCell.word
    gcongr
  · unfold word
    omega

theorem program_meets_sourceProof {lim : Limits} {d : ℕ} {μ : ℕ → ℤ} {free n params U dst : ℕ}
    {color : Coloring.Parameter (inputBits n+1)} {x : Fin n → ℤ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (Hparams : Seg μ params (LightParameterInit.values n)) (hparams : params+19 ≤ free)
    (hw : (lim.space : ℤ) ≤ lim.word) (hR : 4 ≤ radix n)
    (hprior : reportBase free n A B C hsA hsB hsC ≤ dst)
    (hspace : LightWeightedScore.space (dst+4) (maxMod n) (bandSize n) U ≤ lim.space)
    (hword : (word n U : ℤ) ≤ lim.word)
    (hdepth : d+Nat.clog 2 (maxMod n)+8 ≤ lim.depth)
    (hx : ∀ i, |x i| ≤ (U : ℤ)) :
    Meets lim program 20 d
      [n,params,free,EncodedColorPipelineData.finish free n A B C hsA hsB hsC,dst] μ
      (time n U (sortedRecords A B C (bandSize n) (bandSize_pos n) hsA hsB hsC).length)
      (fun r ν => r=(dst : ℤ) ∧
        LightDenseSetup.Stored ν dst
          (GlobalEncoding.representationCap (microHalf (inputBits n)) (blockCount (inputBits n)))
          (ThreeSumColorBudgets.falseScore n A B C hsA hsB hsC) ∧
        EncodedColorPipelineData.Stored ν free n color x A B C hsA hsB hsC ∧ Kept μ ν dst) := by
  let out := EncodedColorPipelineData.finish free n A B C hsA hsB hsC
  let primeHeader := EncodedColorLayout.prime free n (bandSize n)
  let cover := EncodedColorPipelineData.coverBase free n
  let p := EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC
  let av := EncodedColorLayout.av free n
  let ae := EncodedColorLayout.ae free n
  let bv := EncodedColorLayout.bv free n
  let be := EncodedColorLayout.be free n
  let cv := EncodedColorLayout.cv free n
  let ce := EncodedColorLayout.ce free n
  let recs := EncodedColorLayout.rec free n (bandSize n)
  let rs := sortedRecords A B C (bandSize n) (bandSize_pos n) hsA hsB hsC
  let g := bandSize n
  let J := blockCount (inputBits n)
  let aux := EncodedColorPrimeData.poolBase primeHeader
  let s := LightPrimePool.size (primeWindow n)
  have hdst : dst+4 ≤ lim.space := by
    have hh := (le_max_right _ _).trans hspace
    change dst+4+(Nat.log 2 (maxMod n+1)+2) ≤ lim.space at hh
    omega
  obtain ⟨hnA,hnB,hnC⟩ := ThreeSumColorBudgets.normalized_lengths H
  have hrecords := EncodedColorNormalizedData.records_length_le (g := g) (hg := bandSize_pos n)
    (hsA := hsA) (hsB := hsB) (hsC := hsC) hnA hnB hnC
  change rs.length ≤ ColorBandBounds.count n g at hrecords
  have hrs : rs.length=LightEncodedColorPrime.count A.length B.length C.length g := by
    simp only [rs,sortedRecords,records_length]
    rfl
  have hbound (z : ℕ) (hz : z ≤ word n U) : (z : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hz).trans hword
  have hnWord := hbound n (by unfold word; omega)
  have hgWord := hbound g (by unfold word; omega)
  have hJWord := hbound J (by unfold word; omega)
  have hPWord := hbound (maxMod n) (by unfold word; omega)
  have hsWord := hbound s (by unfold word; omega)
  have hcountWord := hbound rs.length (hrecords.trans (by
    change ColorBandBounds.count n (bandSize n) ≤ word n U
    unfold word
    omega))
  have hDenseWord := hbound _ (dense_word_le hnA hnB hnC hrecords)
  have hpmax : p ≤ maxMod n := EncodedColorStageCosts.selected_le_maxMod hR
  have hpWord : (p : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hpmax).trans hPWord
  have hGA := size_le A.length g
  have hGB := size_le B.length g
  have hGC := size_le C.length g
  have hcountZ : (size B.length g : ℤ)*(size C.length g : ℤ)+
      (size A.length g : ℤ)*(size B.length g : ℤ)+(size A.length g : ℤ)*(size C.length g : ℤ) ≤ lim.word := by
    simpa only [hrs,LightEncodedColorPrime.count,Nat.cast_add,Nat.cast_mul] using hcountWord
  have hBC0 : (0 : ℤ) ≤ (size B.length g : ℤ)*(size C.length g : ℤ) := by positivity
  have hAB0 : (0 : ℤ) ≤ (size A.length g : ℤ)*(size B.length g : ℤ) := by positivity
  have hAC0 : (0 : ℤ) ≤ (size A.length g : ℤ)*(size C.length g : ℤ) := by positivity
  have hprefix := prefix_le_report free n A B C hsA hsB hsC
  obtain ⟨hmeta,_,_,_,_,_⟩ := EncodedColorPipelineData.ordered free n A B C hsA hsB hsC
  change primeHeader+6 ≤ cover at hmeta
  have hcover : cover ≤ dst := hprefix.2.trans hprior
  have hfree : free+8 ≤ dst := hprefix.1.trans hprior
  have hout : out+8 ≤ dst := hprior
  have hkey := (cover_end_le_report free n A B C hsA hsB hsC).trans hprior
  have haux := (pool_end_le_report free n A B C hsA hsB hsC).trans hprior
  obtain ⟨hav,hae,hbv,hbe,hcv,hce,_,hrec,_⟩ :=
    EncodedColorLayout.normalized_ends_cover free n g (radix n) (primeWindow n)
  change av+n ≤ cover at hav
  change ae+2+2*n ≤ cover at hae
  change bv+n ≤ cover at hbv
  change be+2+2*n ≤ cover at hbe
  change cv+n ≤ cover at hcv
  change ce+2+2*n ≤ cover at hce
  change recs+4*ColorBandBounds.count n g ≤ cover at hrec
  obtain ⟨readMeta,readCover,_,_,_,_,_,readP⟩ := H.heads_read
  change μ out=(primeHeader : ℤ) at readMeta
  change μ (out+1)=(cover : ℤ) at readCover
  change μ (out+7)=(p : ℤ) at readP
  obtain ⟨readA,readAE,readB,readBE,readC,readCE,readRecs,_⟩ :=
    EncodedColorNormalizedData.heads_read H.normalizedHeads
  change μ free=(av : ℤ) at readA
  change μ (free+1)=(ae : ℤ) at readAE
  change μ (free+2)=(bv : ℤ) at readB
  change μ (free+3)=(be : ℤ) at readBE
  change μ (free+4)=(cv : ℤ) at readC
  change μ (free+5)=(ce : ℤ) at readCE
  change μ (free+6)=(recs : ℤ) at readRecs
  obtain ⟨_,_,_,readAux,readS,_⟩ := H.primes.heads_read
  change μ (primeHeader+3)=(aux : ℤ) at readAux
  change μ (primeHeader+4)=(s : ℤ) at readS
  obtain ⟨_,_,readJ,_,_,readG,_⟩ := EncodedColorParameterData.reads Hparams
  change μ (params+3)=(J : ℤ) at readJ
  change μ (params+17)=(g : ℤ) at readG
  obtain ⟨readNA,readGA⟩ := SourceFiniteInputs.prepared_headers H.normalized.2.1
  obtain ⟨readNB,readGB⟩ := SourceFiniteInputs.prepared_headers H.normalized.2.2.1
  obtain ⟨readNC,readGC⟩ := SourceFiniteInputs.prepared_headers H.normalized.2.2.2.1
  change μ ae=(A.length : ℤ) at readNA
  change μ be=(B.length : ℤ) at readNB
  change μ ce=(C.length : ℤ) at readNC
  change μ (ae+1)=(size A.length g : ℤ) at readGA
  change μ (be+1)=(size B.length g : ℤ) at readGB
  change μ (ce+1)=(size C.length g : ℤ) at readGC
  have hvalueA := SourceFiniteInputs.prepared_read H.normalized.2.1
  have hvalueB := SourceFiniteInputs.prepared_read H.normalized.2.2.1
  have hvalueC := SourceFiniteInputs.prepared_read H.normalized.2.2.2.1
  obtain ⟨hA,hB,hC⟩ := ThreeSumColorBudgets.normalized_values H hx
  have hproduct : ∀ i < s, p*LightPrimePool.prime (primeWindow n) i ≤ maxMod n := by
    intro i hi
    have hp := (BandPrimeScales.modulus_bounds n A.length B.length C.length
      (fun j => A.getD j 0) (fun j => B.getD j 0) (fun j => C.getD j 0) rs).2
    change p ≤ (4*primeWindow n)^primeDepth radix n at hp
    exact (Nat.mul_le_mul hp (LightPrimePool.prime_spec hi).2.2).trans
      (by simpa only [← pow_succ] using BandPrimeScales.resource_modulus_bound hR)
  have hread : ∀ i < s, μ (aux+i)=(LightPrimePool.prime (primeWindow n) i : ℤ) :=
    fun i hi => H.primes.pool.read hi
  have hflags : ∀ r ∈ rs, r.flag=0 ∨ r.flag=1 := fun _ hr => records_flag hr
  have hvalid : ∀ r ∈ rs, r.flag=1 → r.a*g ≤ A.length ∧ r.b*g ≤ B.length ∧ r.c*g ≤ C.length :=
    LightBandPrimeStage.records_valid rfl rfl rfl (bandSize_pos n)
  have out1 : ((out : ℤ)+1).toNat=out+1 := by omega
  have out7 : ((out : ℤ)+7).toNat=out+7 := by omega
  have free1 : ((free : ℤ)+1).toNat=free+1 := by omega
  have free2 : ((free : ℤ)+2).toNat=free+2 := by omega
  have free3 : ((free : ℤ)+3).toNat=free+3 := by omega
  have free4 : ((free : ℤ)+4).toNat=free+4 := by omega
  have free5 : ((free : ℤ)+5).toNat=free+5 := by omega
  have free6 : ((free : ℤ)+6).toNat=free+6 := by omega
  have ae1 : ((ae : ℤ)+1).toNat=ae+1 := by omega
  have be1 : ((be : ℤ)+1).toNat=be+1 := by omega
  have ce1 : ((ce : ℤ)+1).toNat=ce+1 := by omega
  have par3 : ((params : ℤ)+3).toNat=params+3 := by omega
  have par17 : ((params : ℤ)+17).toNat=params+17 := by omega
  have prime3 : ((primeHeader : ℤ)+3).toNat=primeHeader+3 := by omega
  have prime4 : ((primeHeader : ℤ)+4).toNat=primeHeader+4 := by omega
  change Meets lim program 20 d [n,params,free,out,dst] μ (time n U rs.length) _
  apply Meets.of_body (p := 20) (by rfl : program[20]?=some (body 19))
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
    (refine Light.Ends.setToThen (primeHeader : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                readMeta]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [readMeta] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, readMeta] <;> omega)));
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
    (refine Light.Ends.setToThen (cover : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                readCover, out1]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [readCover, out1] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, readCover, out1] <;>
              omega)));
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
    (refine Light.Ends.setToThen (p : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, readP,
                out7]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [readP, out7] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, readP, out7] <;> omega)));
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
    (refine Light.Ends.setToThen (av : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, readA]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [readA] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, readA] <;> omega)));
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
    (refine Light.Ends.setToThen (ae : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, readAE,
                free1]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [readAE, free1] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, readAE, free1] <;> omega)));
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
    (refine Light.Ends.setToThen (bv : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, readB,
                free2]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [readB, free2] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, readB, free2] <;> omega)));
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
    (refine Light.Ends.setToThen (be : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, readBE,
                free3]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [readBE, free3] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, readBE, free3] <;> omega)));
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
    (refine Light.Ends.setToThen (cv : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, readC,
                free4]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [readC, free4] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, readC, free4] <;> omega)));
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
    (refine Light.Ends.setToThen (ce : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, readCE,
                free5]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [readCE, free5] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, readCE, free5] <;> omega)));
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
    (refine Light.Ends.setToThen (recs : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                readRecs, free6]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [readRecs, free6] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, readRecs, free6] <;>
              omega)));
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
    (refine Light.Ends.setToThen (A.length : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                readNA]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [readNA] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, readNA] <;> omega)));
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
    (refine Light.Ends.setToThen (B.length : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                readNB]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [readNB] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, readNB] <;> omega)));
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
    (refine Light.Ends.setToThen (C.length : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                readNC]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [readNC] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, readNC] <;> omega)));
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
    (refine Light.Ends.setToThen (size A.length g : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, readGA,
                ae1]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [readGA, ae1] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, readGA, ae1] <;> omega)));
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
    (refine Light.Ends.setToThen (size B.length g : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, readGB,
                be1]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [readGB, be1] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, readGB, be1] <;> omega)));
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
    (refine Light.Ends.setToThen (size C.length g : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, readGC,
                ce1]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [readGC, ce1] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, readGC, ce1] <;> omega)));
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
    (refine Light.Ends.setToThen (rs.length : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hrs,
                LightEncodedColorPrime.count]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hrs, LightEncodedColorPrime.count] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hrs,
                LightEncodedColorPrime.count] <;>
              omega)));
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
    (refine Light.Ends.setToThen (g : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, readG,
                par17]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [readG, par17] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, readG, par17] <;> omega)));
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
    (refine Light.Ends.setToThen (J : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, readJ,
                par3]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [readJ, par3] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, readJ, par3] <;> omega)));
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
    (refine Light.Ends.setToThen (aux : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, readAux,
                prime3]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [readAux, prime3] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, readAux, prime3] <;>
              omega)));
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
    (refine Light.Ends.setToThen (s : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, readS,
                prime4]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [readS, prime4] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, readS, prime4] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  have hcall := (LightDenseSetup.program_meets (d := d+1) (μ := μ)
    (a := av) (b := bv) (c := cv) (nA := A.length) (nB := B.length) (nC := C.length)
    (g := g) (recs := recs) (q := p) (aux := aux) (s := s) (cover := cover) (free := dst)
    (maxMod := maxMod n) (U := U) (h := microHalf (inputBits n)) (J := J)
    (LightPrimePool.prime (primeWindow n)) rs hw (by omega) (bandSize_pos n)
    EncodedColorPrimeReadyData.selected_pos hpmax (by omega) (by omega) (by omega)
    (by omega) haux hkey hspace hDenseWord H.cover H.normalized.2.2.2.2.2.1 hflags hvalid
    (fun i hi => by rw [hvalueA i hi]; exact hA i hi)
    (fun i hi => by rw [hvalueB i hi]; exact hB i hi)
    (fun i hi => by rw [hvalueC i hi]; exact hC i hi)
    hread (fun _ hi => (LightPrimePool.prime_spec hi).1)
    (fun _ hi _ hj he => LightPrimePool.prime_injective hi hj he) hproduct).append [body 19]
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
      | refine Light.Ends.callToThen (hcall _ (by omega)) ?_ ?_ ?_ ?_
      | refine Light.Ends.callToThen hcall ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, g, J,
                s]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [g, J, s] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, g, J, s] <;> omega)));
    (on_goal -1 =>
        ((rintro result ν ⟨hresult, hdense, _, hkeep⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  have hscore : LightDenseSetup.falseScore (LightPrimePool.prime (primeWindow n)) s p
      A.length B.length C.length g (fun i => μ (av+i)) (fun i => μ (bv+i)) (fun i => μ (cv+i)) rs=
      ThreeSumColorBudgets.falseScore n A B C hsA hsB hsC := by
    unfold ThreeSumColorBudgets.falseScore
    rw [LightDenseSetup.falseScore_eq,LightDenseSetup.falseScore_eq]
    exact BandWeightedScore.score_congr rs hvalueA hvalueB hvalueC
  rw [hscore] at hdense
  exact ⟨hresult,hdense,H.of_kept hkeep hprior,hkeep⟩





end ThreeSum.LightThreeSumReportingSetupDense

end


theorem solution : ∀ {lim : Light.Limits} {d : Nat} {μ : Nat → Int} {free n params U dst : Nat}
  {color :
    ThreeSum.Coloring.Parameter
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (ThreeSum.Scales.inputBits n)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))}
  {x : Fin n → Int} {A B C : List.{0} Int}
  {hsA : @List.Pairwise.{0} Int (fun (x1 x2 : Int) => @LT.lt.{0} Int Int.instLTInt x1 x2) A}
  {hsB : @List.Pairwise.{0} Int (fun (x1 x2 : Int) => @LT.lt.{0} Int Int.instLTInt x1 x2) B}
  {hsC : @List.Pairwise.{0} Int (fun (x1 x2 : Int) => @LT.lt.{0} Int Int.instLTInt x1 x2) C}
  (H : ThreeSum.EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
  (Hparams : Light.Seg μ params (ThreeSum.LightParameterInit.values n))
  (hparams :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) params
        (@OfNat.ofNat.{0} Nat (nat_lit 19) (instOfNatNat (nat_lit 19))))
      free)
  (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (hR :
    @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) (ThreeSum.Scales.radix n))
  (hprior : @LE.le.{0} Nat instLENat (ThreeSum.ThreeSumReportingSetupData.reportBase free n A B C hsA hsB hsC) dst)
  (hspace :
    @LE.le.{0} Nat instLENat
      (ThreeSum.LightWeightedScore.space
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
        (ThreeSum.ArithmeticStageBounds.maxMod n) (ThreeSum.BandScales.bandSize n) U)
      lim.space)
  (hword :
    @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightThreeSumReportingSetupDense.word n U))
      lim.word)
  (hdepth :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
          (Nat.clog (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (ThreeSum.ArithmeticStageBounds.maxMod n)))
        (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
      lim.depth)
  (hx :
    ∀ (i : Fin n),
      @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup (x i))
        (@Nat.cast.{0} Int instNatCastInt U)),
  Light.Meets lim ThreeSum.LightThreeSumReportingSetupDense.program
    (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) d
    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt n)
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt params)
        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt free)
          (@List.cons.{0} Int
            (@Nat.cast.{0} Int instNatCastInt (ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC))
            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt dst) (@List.nil.{0} Int))))))
    μ
    (ThreeSum.LightThreeSumReportingSetupDense.time n U
      (@List.length.{0} ThreeSum.BandCandidateRows.Record
        (ThreeSum.BandRawA.sortedRecords A B C (ThreeSum.BandScales.bandSize n) (ThreeSum.BandScales.bandSize_pos n) hsA
          hsB hsC)))
    fun (r : Int) (ν : Nat → Int) =>
    And (@Eq.{1} Int r (@Nat.cast.{0} Int instNatCastInt dst))
      (And
        (ThreeSum.LightDenseSetup.Stored ν dst
          (ThreeSum.GlobalEncoding.representationCap (ThreeSum.Scales.microHalf (ThreeSum.Scales.inputBits n))
            (ThreeSum.Scales.blockCount (ThreeSum.Scales.inputBits n)))
          (ThreeSum.ThreeSumColorBudgets.falseScore n A B C hsA hsB hsC))
        (And (ThreeSum.EncodedColorPipelineData.Stored ν free n color x A B C hsA hsB hsC) (Light.Kept μ ν dst))) := by
  exact @ThreeSum.LightThreeSumReportingSetupDense.program_meets_sourceProof

#print axioms solution
