-- Prove2me | solution 1 for ThreeSum.LightEncodedColorPipeline.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T18:27:17.574625+00:00
-- url     : https://prove2.me/submissions/6c3a41f6-d682-417f-8b1d-a9af675d96cd

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
import Definitions.Def_ThreeSum1962Source_Bundle15
import Definitions.Def_ThreeSum1962Source_Bundle16
import Definitions.Def_ThreeSum1962Source_Bundle17
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
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import Theorems.Thm_ThreeSum_BandRawA_mem_row
import Theorems.Thm_ThreeSum_EncodedColorParameterData_reads
import Theorems.Thm_ThreeSum_EncodedColorPipelineData_ordered
import Theorems.Thm_ThreeSum_EncodedColorPrimeData_Stored_of_kept
import Theorems.Thm_ThreeSum_Histograms_correlation_histograms
import Theorems.Thm_ThreeSum_LightCoverKeyData_Stored_of_kept
import Theorems.Thm_ThreeSum_LightEncodedColorPrimeHost_program_meets_input
import Theorems.Thm_ThreeSum_LightEncodedColorResult_meets
import Theorems.Thm_ThreeSum_LightEncodedColorWantedHeader_meets
import Theorems.Thm_ThreeSum_LightEncodedColorWantedSources_program_meets
import Theorems.Thm_ThreeSum_LightMinimum_least_value_le
import Theorems.Thm_ThreeSum_LocalCoverBounds_pow_le_choose_mul
import Theorems.Thm_ThreeSum_SourceBandBankData_Stored_of_kept
import Theorems.Thm_ThreeSum_SourceBandBanksCosts_span_count_le_encoderCount
import Theorems.Thm_ThreeSum_SourceBandPairData_Stored_of_kept
import Theorems.Thm_ThreeSum_SourceFiniteData_Normalized_keep


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
namespace ThreeSum.BlockEncoding
end ThreeSum.BlockEncoding
namespace ThreeSum.BlockIndexedQuery
end ThreeSum.BlockIndexedQuery
namespace ThreeSum.BlockSourceSharing
end ThreeSum.BlockSourceSharing
namespace ThreeSum.ColorClassLists
end ThreeSum.ColorClassLists
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
namespace ThreeSum.CyclicFold
end ThreeSum.CyclicFold
namespace ThreeSum.EncodedColorLayout
end ThreeSum.EncodedColorLayout
namespace ThreeSum.EncodedColorNormalizedData
end ThreeSum.EncodedColorNormalizedData
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.GlobalKeyEnumeration
end ThreeSum.GlobalKeyEnumeration
namespace ThreeSum.Karatsuba
end ThreeSum.Karatsuba
namespace ThreeSum.KaratsubaInterface
end ThreeSum.KaratsubaInterface
namespace ThreeSum.LightBlockSourceBatchLayout
end ThreeSum.LightBlockSourceBatchLayout
namespace ThreeSum.LightClassFilter
end ThreeSum.LightClassFilter
namespace ThreeSum.LightHistogram
end ThreeSum.LightHistogram
namespace ThreeSum.LightKaratsuba
end ThreeSum.LightKaratsuba
namespace ThreeSum.LightLocalCoverLayout
end ThreeSum.LightLocalCoverLayout
namespace ThreeSum.LightLocalCoverSchedule
end ThreeSum.LightLocalCoverSchedule
namespace ThreeSum.LightLocalCoverTables
end ThreeSum.LightLocalCoverTables
namespace ThreeSum.LightResidueHistogram
end ThreeSum.LightResidueHistogram
namespace ThreeSum.LightResidues
end ThreeSum.LightResidues
namespace ThreeSum.LightSourceResidues
end ThreeSum.LightSourceResidues
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalGraph
end ThreeSum.LocalGraph
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.Parameters
end ThreeSum.Parameters
namespace ThreeSum.RadixKeyLists
end ThreeSum.RadixKeyLists
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.SourceBandLayout
end ThreeSum.SourceBandLayout
namespace ThreeSum.SourceBandPairData
end ThreeSum.SourceBandPairData
namespace ThreeSum.SourceBuckets
end ThreeSum.SourceBuckets
namespace ThreeSum.StageBounds
end ThreeSum.StageBounds
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum.Switch
end ThreeSum.Switch
namespace ThreeSum.TrimScales
end ThreeSum.TrimScales
namespace ThreeSum.WantedPairs
end ThreeSum.WantedPairs
namespace ThreeSum.WantedResidueKeys
end ThreeSum.WantedResidueKeys
namespace ThreeSumApsp
end ThreeSumApsp

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

/-- The mean is exact for every table, with no hash-uniformity assumption. -/
theorem exists_balanced_offset (F H : G → ℕ) :
    ∃ d, Fintype.card G * correlation F H d ≤ (∑ k, F k) * (∑ k, H k) := by
  by_contra! h
  have hs : (∑ _d : G, (∑ k, F k) * (∑ k, H k)) <
      ∑ d, Fintype.card G * correlation F H d := by
    exact sum_lt_sum_of_nonempty (by simp) (by simpa using h)
  simp only [sum_const, nsmul_eq_mul, card_univ, ← mul_sum, sum_correlation] at hs
  exact (lt_irrefl _ hs)























end ThreeSum.Balancing

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

/-- More time and a weaker conclusion. -/
theorem Meets.mono (h : Meets lim P p d vals μ T R) (hT : T ≤ T') (hR : ∀ r μ', R r μ' → R' r μ') :
    Meets lim P p d vals μ T' R' := by
  obtain ⟨body, hp, he⟩ := h
  exact ⟨body, hp, he.mono hT fun _ => hR _ _⟩

/-- A specification holds with every larger bound on the time. -/
theorem Meets.mono_time (h : Meets lim P p d vals μ T R) (hT : T ≤ T' := by omega) :
    Meets lim P p d vals μ T' R :=
  h.mono hT fun _ _ hR => hR






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































































/-- A segment only depends on its own cells. -/
theorem Seg.congr (h : Seg μ a l) (he : ∀ i < l.length, μ' (a + i) = μ (a + i)) : Seg μ' a l :=
  fun i hi => by rw [he i hi, h i hi]

























/-- A segment all of whose cells are kept. -/
theorem Seg.of_sameOn {K : ℕ → Prop} (h : Seg μ b l) (hs : SameOn K μ μ')
    (hK : ∀ i < l.length, K (b + i)) : Seg μ' b l := h.congr fun i hi => hs _ (hK i hi)





































































































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
# Finite numerical bounds for the local cover

The graph degree bound follows from exact finite cardinalities: the degree
is no larger than the number of vertices, while vertices times degree equal
outputs times representations per output.  This avoids any approximation
of factorials.  The prime-interval and normalized first-moment estimates
are stated explicitly in terms of the concrete binomial coefficients.
-/

namespace ThreeSum.LocalCoverBounds

open scoped BigOperators




































theorem concrete_output_gt_pow {h : ℕ} (hh : 0 < h) :
    2 ^ (2 * h) < outputCount (512 * h) h := by
  have hlo : 256 ^ (2 * h) ≤ outputCount (512 * h) h := by
    simpa [outputCount, show 256 * (2 * h) = 512 * h by omega] using
      pow_le_choose_mul 256 (2 * h)
  exact ((Nat.pow_lt_pow_iff_left (by omega : 2 * h ≠ 0)).mpr (by decide)).trans_le hlo

























































































/-! ## A deterministic selected prime -/















































































/-! ## Exact integer rounding of the separable bucket cap -/































/-! ## The actual local parameters at `L=512*h` -/





























































end ThreeSum.LocalCoverBounds

end

section


/-!
# Literal global-output records behind the radix key array

Local records use the verified layer enumerator's order and retain every
schedule occurrence. Cartesian extension enumerates each original global
output once. Mapping to integers may introduce equal values; the key array
retains all of those separate incidences.
-/

namespace ThreeSum.GlobalKeyEnumeration

open GlobalEncoding LocalGraph LocalCoverBounds LocalHashMoments
open RadixKeyLists
open scoped BigOperators

set_option maxHeartbeats 1800000


































































































theorem globalKeys_length (h J : ℕ) :
    (globalKeys h J).length=scheduleSize h^J*outputCount (512*h) h^J := by
  rw [globalKeys_eq_map,List.length_map,globalRecords_length]































end ThreeSum.GlobalKeyEnumeration

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












theorem size_mono {n m g : ℕ} (h : n ≤ m) : size n g ≤ size m g := by
  by_cases hn : n = 0
  · simp [size,hn]
  · have hm : m ≠ 0 := by omega
    have hd := Nat.div_le_div_right (c := g) (show n-1 ≤ m-1 by omega)
    simp only [size,if_neg hn,if_neg hm]
    omega

/-- A finite ceiling bound, including the empty input. -/
theorem size_mul_le (n g : ℕ) : size n g*g ≤ n+g := by
  by_cases hn : n = 0
  · simp [size,hn]
  · have hd := Nat.div_mul_le_self (n-1) g
    simp only [size,if_neg hn,Nat.add_mul,Nat.one_mul]
    omega

























theorem length_le (n g i : ℕ) : stop n g i-start g i ≤ g := by
  have hle : stop n g i ≤ (i+1)*g := min_le_right _ _
  unfold start
  simp only [Nat.add_mul,Nat.one_mul] at hle
  omega


















































end ThreeSum.BandPartition

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












































































































end ThreeSum.LightResidues

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












theorem sum_signedHistogram {p : ℕ} [NeZero p]
    (c : ℤ) (values : ℕ → ℤ) (n : ℕ) :
    (∑ z : ZMod p, signedHistogram p c values n z) = n := by
  unfold signedHistogram
  rw [Histograms.sum_histogram]
  simp















































































































































end ThreeSum.LightResidueHistogram

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
# Exact relocation of closed verified procedure libraries

Every procedure call is shifted by the same list offset. The structural
execution proof preserves the exact initial/final states, runtime, memory
addresses, values, and depth budget. It permits composition of independently
verified fixed programs without assuming a new implementation contract.
-/

namespace ThreeSum.ReportingHostRelocation

open Light












theorem lookup {P : Program} {p : ℕ} {body : Stmt} (h : P[p]? = some body) (prefixProgram : Program) :
    (program prefixProgram P)[prefixProgram.length+p]? = some (relocate prefixProgram.length body) := by
  apply getElem?_append_length_add
  rw [List.getElem?_map,h]
  rfl

theorem exec {lim : Limits} {P : Program} {d : ℕ} {s : Stmt} {σ σ' : State} {c : ℕ}
    (h : Exec lim P d s σ σ' c) (prefixProgram : Program) :
    Exec lim (program prefixProgram P) d (relocate prefixProgram.length s) σ σ' c := by
  induction h with
  | skip => exact .skip
  | set h => exact .set h
  | store h₁ h₂ h₃ => exact .store h₁ h₂ h₃
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | iteTrue h₁ h₂ _ ih => exact .iteTrue h₁ h₂ ih
  | iteFalse h₁ h₂ _ ih => exact .iteFalse h₁ h₂ ih
  | whileFalse h₁ h₂ => exact .whileFalse h₁ h₂
  | whileTrue h₁ h₂ _ _ ih₁ ih₂ => exact .whileTrue h₁ h₂ ih₁ ih₂
  | call h₁ h₂ h₃ _ ih => exact .call h₁ (lookup h₂ prefixProgram) h₃ ih

theorem ends {lim : Limits} {P : Program} {d : ℕ} {s : Stmt} {σ : State} {T : ℕ} {Q : State → Prop}
    (h : Ends lim P d s σ T Q) (prefixProgram : Program) :
    Ends lim (program prefixProgram P) d (relocate prefixProgram.length s) σ T Q := by
  obtain ⟨σ',c,he,hc,hq⟩ := h
  exact ⟨σ',c,exec he prefixProgram,hc,hq⟩

theorem meets {lim : Limits} {P : Program} {p d : ℕ} {vals : List ℤ} {μ : ℕ → ℤ}
    {T : ℕ} {R : ℤ → (ℕ → ℤ) → Prop} (h : Meets lim P p d vals μ T R) (prefixProgram : Program) :
    Meets lim (program prefixProgram P) (prefixProgram.length+p) d vals μ T R := by
  obtain ⟨body,hbody,he⟩ := h
  exact ⟨relocate prefixProgram.length body,lookup hbody prefixProgram,ends he prefixProgram⟩

end ThreeSum.ReportingHostRelocation

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






















































































theorem prime_spec {y i : ℕ} (hi : i < size y) :
    Nat.Prime (prime y i) ∧ y < prime y i ∧ prime y i ≤ 4*y :=
  mem_values.mp (prime_mem hi)











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
# Exact A-value incidences of the physical band-owner catalog

Each successful owner contributes only its A band. Labels retain the
physical owner slot and the coordinate in the retained sorted A array.
Equal values and equal triples in different owner slots remain distinct.
-/

namespace ThreeSum.BandRawA

open BandCandidateRows BandEnumeration BandPartition

set_option maxHeartbeats 1600000
set_option maxRecDepth 7000





























theorem row_length (n g owner : ℕ) (r : Record) :
    (row n g owner r).length=if r.flag=1 then bandLength n g r.a else 0 := by
  unfold row
  split_ifs <;> simp

theorem row_length_le (n g owner : ℕ) (r : Record) : (row n g owner r).length ≤ g := by
  rw [row_length]
  split_ifs
  · exact BandPartition.length_le n g r.a
  · omega










theorem firstRows_succ (n g : ℕ) (rs : List Record) (i : ℕ) :
    firstRows n g rs (i+1)=firstRows n g rs i++row n g i (rs.getD i default) := by
  simp only [firstRows,List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil]

@[simp] theorem count_zero (n g : ℕ) (rs : List Record) : count n g rs 0=0 := rfl

theorem count_succ (n g : ℕ) (rs : List Record) (i : ℕ) :
    count n g rs (i+1)=count n g rs i+(row n g i (rs.getD i default)).length := by
  simp only [count,firstRows_succ,List.length_append]







theorem count_bound (n g : ℕ) (rs : List Record) (i : ℕ) : count n g rs i ≤ g*i := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [count_succ]
    have hh := row_length_le n g i (rs.getD i default)
    nlinarith

theorem items_length_le (n g : ℕ) (rs : List Record) : (items n g rs).length ≤ g*rs.length :=
  count_bound n g rs rs.length






























theorem mem_firstRows {n g i : ℕ} {rs : List Record} {l : Label} :
    l ∈ firstRows n g rs i ↔
      l.owner < i ∧ l ∈ row n g l.owner (rs.getD l.owner default) := by
  constructor
  · intro hl
    obtain ⟨owner,ho,hl⟩ := List.mem_flatMap.mp hl
    have he := (mem_row.mp hl).2.1
    subst owner
    exact ⟨List.mem_range.mp ho,hl⟩
  · rintro ⟨ho,hl⟩
    exact List.mem_flatMap.mpr ⟨l.owner,List.mem_range.mpr ho,hl⟩

theorem position_lt {n g i : ℕ} {rs : List Record} {l : Label}
    (hl : l ∈ firstRows n g rs i) : l.position < n := by
  have hh := (mem_row.mp (mem_firstRows.mp hl).2).2.2.2
  exact hh.trans_le (stop_le n g _)




theorem values_bounded {n g i U : ℕ} {rs : List Record} {f : ℕ → ℤ}
    (hf : ∀ j < n, |f j| ≤ (U : ℤ)) :
    ∀ v ∈ values f (firstRows n g rs i), |v| ≤ (U : ℤ) := by
  intro v hv
  obtain ⟨l,hl,rfl⟩ := List.mem_map.mp hv
  exact hf l.position (position_lt hl)

































end ThreeSum.BandRawA

end

section


/-!
# Problems, solvers, and the interpretation of "is solved in time T" in the light language

A *task* is a problem together with a calling convention: which arguments a procedure gets, what the
memory holds when it is called, and what the result and the memory have to be when it returns.
`Solves task P p T need` says that procedure number `p` of the program `P` solves the task within
`T` steps, if the limits of the run allow for `need`.  A reduction of the paper is a *host*: a
procedure that calls an arbitrary solver of another task.

Conventions.

* A solver gets sizes, a bound `U` on the absolute values of the numbers, the addresses of its
  arrays, and as last argument the free pointer `fr`.  All inputs and outputs lie below `fr`.  The
  solver may write its output segments and any cell from `fr` on, and no other cell.  Nothing is
  assumed about the cells from `fr` on, so a solver can be called again and again.
* A solver has to be correct for every valid bound `U` that it is given.
* A solver is a pair of a program and a procedure number.  What is proved about it holds for every
  program that begins with this program, so a host appends its own procedures.

A `Task` is a problem whose time and need depend on a size and a bound.  `TaskN` and `SolvesN` are
the same notions with a list of parameters.
-/

@[expose] public section

namespace Light

open ThreeSumApsp

/-! ## Limits -/






























/-! ## Specifications of single routines -/

/-- A list below fr stays where it is if nothing below fr changes. -/
theorem Seg.of_kept {μ μ' : ℕ → ℤ} {a fr : ℕ} {l : List ℤ} (h : Seg μ a l) (hk : Kept μ μ' fr)
    (hle : a + l.length ≤ fr) : Seg μ' a l :=
  h.of_sameOn hk fun i hi => show a + i < fr by omega

/-! ## Tasks and solvers -/
























































































/-! ## Hosts -/






















/-! ## Tasks with a list of parameters -/














































end Light

end
end

section


/-!
# An actual minimum scan of the fast cyclic correlation

The returned offset obeys the exact mean bound for the supplied histograms.
The choice is made by a fixed program, not by an existential witness in the
proof. The histograms themselves are the procedure's array inputs.
-/

namespace ThreeSum.LightBalancedOffset

open Light Karatsuba CyclicFold LightKaratsuba Finset
open scoped BigOperators







theorem offset_balanced {p : ℕ} [NeZero p] (F H : ZMod p → ℕ) :
    p * Balancing.correlation F H (offset F H : ZMod p) ≤
      (∑ z, F z) * (∑ z, H z) := by
  obtain ⟨z, hz⟩ := Balancing.exists_balanced_offset F H
  have hmin := LightMinimum.least_value_le
    (fun r => (Balancing.correlation F H (r : ZMod p) : ℤ)) p z.val (ZMod.val_lt z)
  have hminNat : Balancing.correlation F H (offset F H : ZMod p) ≤
      Balancing.correlation F H z := by
    simpa only [offset, ZMod.natCast_zmod_val, Nat.cast_le] using hmin
  have hcard : Fintype.card (ZMod p) = p := ZMod.card p
  rw [hcard] at hz
  exact (Nat.mul_le_mul_left p hminNat).trans hz








variable {lim : Limits} {P : Program} {d : ℕ}






































































end ThreeSum.LightBalancedOffset

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
# Actual vertex and trimmed-bucket scales

The local prime and bucket cap are the computable finite selections from
`LocalCoverBounds`.  Their logarithmic rates are derived from those exact
definitions and the exact integer schedule in `Scales`.
-/

namespace ThreeSum.TrimScales

open Filter Real ThreeSum.Scales
open scoped Topology






















noncomputable section





















































































































































theorem localLength_pos (h : ℕ) : 0 < localLength h := by
  simp only [localLength, LocalHashMoments.localSchedule_length]
  positivity










































































































































end

end ThreeSum.TrimScales

end

section


/-!
# The executable band size and its exact exponent

The band numerator is the integer ceiling of the square root of the actual
typed output count. The denominator is `2^(mu/20)`. Since the block schedule
has `20 ∣ mu`, the denominator exponent has no divisibility error.
-/

namespace ThreeSum.BandScales

open Filter Real ThreeSum.Scales
open scoped Topology











theorem typedOutputs_pos (n : ℕ) : 0 < typedOutputs n := by
  unfold typedOutputs
  exact Nat.pow_pos (Nat.choose_pos (by omega))



























noncomputable section

































































































































end

end ThreeSum.BandScales

end

section


/-!
# Actual finite hierarchy counts

These are the binomial counts used by the concrete microblock hierarchy.
Every prefix partition is included.  The integer switch and its rounding
allowance are applied before any asymptotic estimate is made.  The counts
in this module are combinatorial work counts; the implementation's operation
counts, raw wanted incidences, and false-mass bounds are separate interfaces.
-/

namespace ThreeSum.CostLedger

open Filter Set Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.Switch
open scoped Topology BigOperators

set_option maxHeartbeats 400000






















theorem bandCount_mul_bounds (n : ℕ) :
    n ≤ BandScales.bandSize n * bandCount n ∧
      BandScales.bandSize n * bandCount n < n + BandScales.bandSize n := by
  constructor
  · exact (ceilDiv_le_iff_le_mul (a := BandScales.bandSize n) (b := n)
      (c := bandCount n) (BandScales.bandSize_pos n)).mp le_rfl
  · have h := Nat.div_mul_le_self (n + BandScales.bandSize n - 1) (BandScales.bandSize n)
    simp only [bandCount, Nat.ceilDiv_eq_add_pred_div]
    rw [Nat.mul_comm (BandScales.bandSize n)]
    have hpos := BandScales.bandSize_pos n
    omega
















noncomputable section

















































































































































end
end ThreeSum.CostLedger

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



















































































end ThreeSum.BandPrimeScales

end

section


/-!
# Original-input residue keys with a carry offset

The source histogram uses `(x % p + shift) % m`, with two independently
chosen moduli. This procedure computes both remainders from each original
signed input and retains every incidence, including duplicate values.
-/

namespace ThreeSum.LightSourceResidues

open Light

set_option maxHeartbeats 1200000
set_option maxRecDepth 10000




































variable {lim : Limits} {P : Program} {d : ℕ}











































































































theorem time_bound (n p U D : ℕ) :
    time n p U D ≤
      254*n*(Nat.log 2 (U+1)+Nat.log 2 (p+D+1)+1)+6 := by
  unfold time LightResidues.residueBudget
  nlinarith

end ThreeSum.LightSourceResidues

end

section


/-!
# Original-input histograms give the exact independently trimmed sources

The histogram keys retain the first modular reduction and the signed carry
offset. Looking up the endpoint's final residue therefore counts precisely
the original divisibility condition in `BlockEncoding`. An explicit finite
enumeration accounts for every original input incidence once.
-/

namespace ThreeSum.BlockSourceEncoding

open Finset BlockEncoding GlobalEncoding LocalCoverBounds LightSourceResidues
open scoped BigOperators

set_option maxHeartbeats 1000000



































theorem modulus_pos (h J : ℕ) : 0 < modulus h J := pow_pos (localPrime_pos h) J




section OriginalSources

variable {β : Type*} [DecidableEq β]



























end OriginalSources

end ThreeSum.BlockSourceEncoding

end

section


/-!
# Exact sharing of source transforms and the encoder ledger

Source stages are indexed by a source band and an occurrence vector. The
output subset and the three-valued A lift do not enter the source function.
Compact table and zeta charges below match the existing `encoderCount`
without introducing a factor for all complete global outputs.
-/

namespace ThreeSum.BlockSourceSharing

open BlockEncoding GlobalEncoding BlockIndexedQuery SubsetAddress
open Scales TrimScales CostLedger StageBounds































theorem occurrence_card (h J : ℕ) : Fintype.card (Occurrences h J) = scheduleSize h^J := by
  simp only [Occurrences,Occurrence,Fintype.card_fun,Fintype.card_fin]

theorem occurrence_card_eq_scheduleCount (n : ℕ) :
    Fintype.card (Occurrences (microHalf (inputBits n)) (blockCount (inputBits n))) = scheduleCount n := by
  rw [occurrence_card,scheduleCount,replicatedHalf,localLength,scheduleSize_eq_length]

theorem width_eq (n : ℕ) :
    blockCount (inputBits n)*(512*microHalf (inputBits n)) = 256*mu n := by
  unfold mu totalSize microSize microHalf
  ring

theorem cutoff_eq (n : ℕ) :
    2*microHalf (inputBits n)*blockCount (inputBits n) = mu n := by
  unfold mu totalSize microSize microHalf
  ring




























































end ThreeSum.BlockSourceSharing

end

section


/-!
# Exact shared-bank dimensions and charge of the actual catalog

There are two stage families for each original band and occurrence vector.
The decoder and bank-loop overhead are included. Neither the number of
complete output subsets nor the three-valued query lift multiplies this
construction.
-/

namespace ThreeSum.BlockSourceCatalogCosts

open Scales TrimScales StageBounds CostLedger BlockSourceSharing SubsetAddress
open LightBlockSourceBatchLayout

theorem count_eq_scheduleCount (n : ℕ) :
    LightBlockSourceCatalog.count (microHalf (inputBits n)) (blockCount (inputBits n)) =
      scheduleCount n := by
  unfold LightBlockSourceCatalog.count
  rw [← occurrence_card,occurrence_card_eq_scheduleCount]






























































































end ThreeSum.BlockSourceCatalogCosts

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


/-!
# The retained cover, output layers, and exact global key array

This bundle is produced by the actual cover/key host and remains valid when
later phases use its computed next free address. In particular the output
index decoder can read the original layer masks without reconstructing them.
-/

namespace ThreeSum.LightCoverKeyData

open Light GlobalEncoding GlobalKeyEnumeration LocalCoverBounds
open LightLocalCoverTables LightLocalCoverLayout LightLocalCoverSchedule

set_option maxHeartbeats 1200000
set_option maxRecDepth 8000




theorem global_length (h J : ℕ) : (globalKeys h J).length=LightGlobalKeys.localCount h^J := by
  simp only [globalKeys_length,LightGlobalKeys.localCount,mul_pow]
































































end ThreeSum.LightCoverKeyData

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








/-- The actual selected offset satisfies the exact raw-incidence mean bound,
including duplicate keys in either original array. -/
theorem selected_pairMass_bound (p : ℕ) [NeZero p] (left right : ℕ → ℤ)
    (nLeft nRight : ℕ) :
    p * Histograms.pairMass (Finset.range nLeft) (Finset.range nRight)
      (fun i => (left i : ZMod p)) (fun i => (right i : ZMod p))
      (fun _ => 1) (fun _ => 1) (selected p left right nLeft nRight : ZMod p) ≤
        nLeft*nRight := by
  have h := LightBalancedOffset.offset_balanced (signedHistogram p 1 right nRight)
    (signedHistogram p 1 left nLeft)
  rw [sum_signedHistogram,sum_signedHistogram] at h
  change p * Balancing.correlation _ _ (selected p left right nLeft nRight : ZMod p) ≤ _ at h
  unfold signedHistogram at h
  rw [Histograms.correlation_histograms] at h
  simpa only [one_mul,Nat.mul_comm] using h













































variable {lim : Limits} {P : Program} {d : ℕ}








































































































































end ThreeSum.LightOriginalOffset

end

section


/-!
# The actual array-selected offset balances original output records

The program's right histogram is indexed by literal key-array positions.
This module transports that count bijectively to the original global output
type, retaining distinct outputs that happen to have equal integer keys.
-/

namespace ThreeSum.GlobalKeyOffset

open GlobalEncoding GlobalKeyEnumeration
open scoped BigOperators

set_option maxHeartbeats 1800000




















































theorem residue_relation_iff (p : ℕ) (left right d : ℤ) :
    (right : ZMod p)-(left : ZMod p)=(d : ZMod p) ↔ (p : ℤ) ∣ left+d-right := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd,Int.cast_sub,Int.cast_add,sub_eq_zero]
  constructor
  · intro hh
    simpa only [add_comm] using (sub_eq_iff_eq_add.mp hh).symm
  · intro hh
    apply sub_eq_iff_eq_add.mpr
    simpa only [add_comm] using hh.symm







end ThreeSum.GlobalKeyOffset

end

section


/-!
# Original A positions and all three guarded lifts

The physical key order is lift-major, preserving every original position.
The selected-offset count is transported to the unchanged guarded wanted
labels used by raw reporting, including repeated input values.
-/

namespace ThreeSum.RawAKeyLists

open GlobalEncoding RawIncidences GlobalKeyEnumeration LocalHashMoments LocalCoverBounds
open scoped BigOperators

set_option maxHeartbeats 900000






















theorem keys_length (P : ℤ) (xs : List ℤ) : (keys P xs).length=3*xs.length := by
  rw [keys,List.length_map,records_length]











































































































end ThreeSum.RawAKeyLists

end

section


/-!
# Exact output-sensitive residue join semantics

The join visits a stored right-index fiber once for each left input
position. Its output is the literal list of matching position pairs.
The count is the guarded wanted mass when the left codes include the
selected common shift and the right codes are the original output keys.
-/

namespace ThreeSum.WantedPairs

open Light SourceBuckets
open scoped BigOperators

set_option maxHeartbeats 1200000




@[simp] theorem count_zero (left right : ℕ → ℕ) (NR : ℕ) : count left right NR 0=0 := by
  simp [count]

theorem count_succ (left right : ℕ → ℕ) (NR n : ℕ) :
    count left right NR (n+1)=count left right NR n+LightHistogram.count right (left n) NR :=
  Finset.sum_range_succ _ _













































































































theorem residue_eq_iff {M : ℕ} (hM : 0 < M) (a b d : ℤ) :
    LightResidues.residue M 1 b=LightResidues.residue M 1 (a+d) ↔ (M : ℤ) ∣ a+d-b := by
  rw [← Nat.cast_inj (R := ℤ),LightResidues.residue_cast hM,
    LightResidues.residue_cast hM,one_mul,one_mul]
  exact Int.modEq_iff_dvd







































end ThreeSum.WantedPairs

end

section


/-!
# A literal output-sensitive join of original-position residue arrays

The host reads each left code and visits only its matching retained right
fiber. Recursion gives a sum of actual row costs; it never charges or scans
the full left/right Cartesian product. The output contains every matching
original-position pair exactly once.
-/

namespace ThreeSum.LightWantedJoin

open Light SourceBuckets WantedPairs

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000


















theorem time_bound (left right : ℕ → ℕ) (NR n : ℕ) :
    time left right NR n ≤ 400*(n+count left right NR n+1) := by
  induction n with
  | zero => simp [time]
  | succ n ih => rw [time,count_succ]; unfold LightWantedRow.time; omega

variable {lim : Limits} {P : Program}












































































































end ThreeSum.LightWantedJoin

end

section


/-!
# The actual residue scans and the selected wanted mass

The two-remainder source scanner specializes to an ordinary shifted residue
when its moduli agree. Its actual fiber count is exactly the incidence mass
minimized by the original signed-array offset program.
-/

namespace ThreeSum.WantedResidueKeys

open Light
open scoped BigOperators



theorem code_eq_residue (M : ℕ) (shift x : ℤ) :
    code M shift x=LightResidues.residue M 1 (x+shift) := by
  simp only [code,LightSourceResidues.key,LightResidues.residue,one_mul]
  congr 1
  rw [Int.add_emod,Int.emod_emod,← Int.add_emod]




theorem code_eq_iff {M : ℕ} (hM : 0 < M) (a b shift : ℤ) :
    code M 0 b=code M shift a ↔ (M : ℤ) ∣ a+shift-b := by
  rw [code_eq_residue,code_eq_residue,add_zero]
  exact WantedPairs.residue_eq_iff hM a b shift




theorem total_eq_pairMass (M : ℕ) (hM : 0 < M) (left right : ℕ → ℤ)
    (NL NR : ℕ) (shift : ℤ) :
    total M left right NL NR shift =
      Histograms.pairMass (Finset.range NL) (Finset.range NR)
        (fun i => (left i : ZMod M)) (fun j => (right j : ZMod M))
        (fun _ => 1) (fun _ => 1) (shift : ZMod M) := by
  unfold total WantedPairs.count LightHistogram.count Histograms.pairMass
  simp only [Finset.card_eq_sum_ones,Finset.sum_filter,one_mul,
    code_eq_iff hM,GlobalKeyOffset.residue_relation_iff]

theorem selected_total_bound (M : ℕ) [NeZero M] (left right : ℕ → ℤ) (NL NR : ℕ) :
    M*total M left right NL NR (LightOriginalOffset.selected M left right NL NR) ≤ NL*NR := by
  rw [total_eq_pairMass M (Nat.pos_of_ne_zero (NeZero.ne M))]
  simpa only [Int.cast_natCast] using LightOriginalOffset.selected_pairMass_bound M left right NL NR



















end ThreeSum.WantedResidueKeys

end

section


/-!
# Actual contiguous buckets from a generic residue-code array

This fixed program constructs its own count histogram, then exact prefix
offsets and an index scatter. No caller-supplied bucket lengths or lists are
assumed. It is shared by source extraction and output-sensitive residue joins.
-/

namespace ThreeSum.LightSourceBucketBuild

open Light SourceBuckets LightHistogram

set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
















variable {lim : Limits} {P : Program} {d : ℕ}













































theorem time_bound (N M : ℕ) : time N M ≤ 300*(N+M+1) := by
  unfold time histogramTime countTime fillTime LightSourceBucketFromHistogram.time
    LightSourceBucketOffsets.time LightSourceBucketScatter.time
  omega

end ThreeSum.LightSourceBucketBuild

end

section


/-!
# Packed generic residue buckets from four scalar arguments

Only the code-array base, item count, positive residue count, and free pointer are
supplied. The program computes every histogram/offset/cursor/index address
and returns the next free address. Its exact fibers serve both source
reporting and the wanted-record residue join.
-/

namespace ThreeSum.LightSourceBucketSetup

open Light SourceBuckets LightHistogram

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000






















variable {lim : Limits} {P : Program} {d : ℕ}








































theorem time_bound (N M : ℕ) : time N M ≤ 500*(N+M+1) := by
  have hb := LightSourceBucketBuild.time_bound N M
  unfold time
  omega

end ThreeSum.LightSourceBucketSetup

end

section


/-!
# Original signed arrays to an actual shifted wanted-pair array

The closed host computes all residue and bucket addresses, runs both signed
scans, builds the right fibers, and executes the output-sensitive join. Four
header cells retain the pair count, pair-array address, next free address and
the actual shift. No residue array, histogram or matching list is supplied.
-/

namespace ThreeSum.LightWantedSetup

open Light WantedResidueKeys

set_option maxHeartbeats 2200000
set_option maxRecDepth 10000





















































variable {lim : Limits}























































































































theorem time_bound (M : ℕ) (left right : ℕ → ℤ) (NL NR U D : ℕ) (shift : ℤ) :
    time M left right NL NR U D shift ≤
      2000*(NL+NR+M+total M left right NL NR shift+1)*
        (Nat.log 2 (U+1)+Nat.log 2 (M+D+1)+1) := by
  have hL := LightSourceResidues.time_bound NL M U D
  have hR := LightSourceResidues.time_bound NR M U D
  have hB := LightSourceBucketSetup.time_bound NR M
  have hJ := LightWantedJoin.time_bound (fun i => code M shift (left i))
    (fun j => code M 0 (right j)) NR NL
  change LightWantedJoin.time _ _ NR NL ≤ 400*(NL+total M left right NL NR shift+1) at hJ
  unfold time
  nlinarith

end ThreeSum.LightWantedSetup

end

section


/-!
# Executable balancing followed by the complete wanted-pair join

The host chooses the common shift from the two original signed arrays and
then builds every matching original-position pair. The returned count obeys
the exact incidence mean bound. The offset and the residue/bucket inputs are
computed by the closed program, with the same duplicate multiplicities.
-/

namespace ThreeSum.LightBalancedWanted

open Light WantedResidueKeys

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000

























variable {lim : Limits}



























































theorem total_le_div (M : ℕ) [NeZero M] (left right : ℕ → ℤ) (NL NR : ℕ) :
    total M left right NL NR (LightOriginalOffset.selected M left right NL NR) ≤ NL*NR/M := by
  apply (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero (NeZero.ne M))).mpr
  simpa only [Nat.mul_comm] using selected_total_bound M left right NL NR

theorem time_bound (M : ℕ) [NeZero M] (left right : ℕ → ℤ) (NL NR U : ℕ) :
    time M left right NL NR U ≤ LightOriginalOffset.time M NL NR U+
      2000*(NL+NR+M+NL*NR/M+1)*(Nat.log 2 (U+1)+Nat.log 2 (M+M+1)+1)+100 := by
  have hh := LightWantedSetup.time_bound M left right NL NR U M
    (LightOriginalOffset.selected M left right NL NR)
  have hc := total_le_div M left right NL NR
  calc
    time M left right NL NR U ≤ LightOriginalOffset.time M NL NR U+
      2000*(NL+NR+M+total M left right NL NR (LightOriginalOffset.selected M left right NL NR)+1)*
        (Nat.log 2 (U+1)+Nat.log 2 (M+M+1)+1)+100 := by unfold time; omega
    _ ≤ _ := by gcongr

end ThreeSum.LightBalancedWanted

end

section


/-!
# Actual cover construction, lifted A keys, and balanced wanted records

This closed program runs the local-cover initializer and global key product,
constructs all three lifts of the supplied A incidences, selects the common
offset, and emits precisely the matching position pairs. Every dimension and
output address is read or computed. The retained cover, layers and coefficient
tables are available to the source-bank and output-decoding phases afterwards.
-/

namespace ThreeSum.LightGuardedWanted

open Light GlobalEncoding GlobalKeyEnumeration LocalCoverBounds

set_option maxHeartbeats 2400000
set_option maxRecDepth 10000








































theorem selected_eq (P M h J : ℕ) [NeZero M] (xs : List ℤ) :
    LightOriginalOffset.selected M (left P xs) (right h J) (3*xs.length) (totalKeys h J)=
      RawAKeyLists.selected M P xs h J := by
  unfold RawAKeyLists.selected GlobalKeyOffset.selected
  rw [RawAKeyLists.keys_length,LightCoverKeyData.global_length]
  rfl






















variable {lim : Limits}






















































































end ThreeSum.LightGuardedWanted

end

section


/-! # Packed original-band histograms and exact physical residue fibers -/

namespace ThreeSum.SourceBandLayout

open BandPartition LightHistogram SourceBuckets































theorem capacity_product_le (n g : ℕ) (hg : 0 < g) : size n g*cap n g ≤ 2*n := by
  by_cases hgn : g ≤ n
  · rw [cap,min_eq_right hgn]
    exact (size_mul_le n g).trans (by omega)
  · by_cases hn : n=0
    · simp [hn,cap]
    · have hdiv : (n-1)/g=0 := Nat.div_eq_of_lt (by omega)
      simp only [cap,min_eq_left (by omega : n ≤ g),size,if_neg hn,hdiv,zero_add,one_mul]
      omega





























theorem work_bound (base n g m : ℕ) (hg : 0 < g) :
    work base n g m ≤ base+4*n+size n g*(3*m+7) := by
  have hc := capacity_product_le n g hg
  unfold work hist data stride
  nlinarith









































end ThreeSum.SourceBandLayout

end

section


/-! # Two retained original-band catalogs and one shared empty histogram -/

namespace ThreeSum.SourceBandPairData

open Light BandPartition






theorem work_ge (base n g m : ℕ) : base ≤ SourceBandLayout.work base n g m := by
  unfold SourceBandLayout.work SourceBandLayout.hist SourceBandLayout.data
  omega

theorem ordered (base NL NR g m : ℕ) :
    leftBase base ≤ rightBase base NL g m ∧
    rightBase base NL g m ≤ zeroBase base NL NR g m ∧
    zeroBase base NL NR g m < next base NL NR g m := by
  exact ⟨work_ge _ _ _ _,work_ge _ _ _ _,by unfold next; omega⟩










































































end ThreeSum.SourceBandPairData

end

section


/-! # Padded histogram selection for independently chosen original bands -/

namespace ThreeSum.SourceBandPairSlices

open Light BandPartition SourceBandLayout SourceBandPairData





















































theorem heads_read {μ : ℕ → ℤ} {fL fR : ℕ → ℤ} {base NL NR g p m : ℕ} {shift : ℤ}
    (H : Stored μ fL fR base NL NR g p m shift) :
    μ base=(leftBase base : ℤ) ∧ μ (base+1)=(size NL g : ℤ) ∧
    μ (base+2)=(rightBase base NL g m : ℤ) ∧ μ (base+3)=(size NR g : ℤ) ∧
    μ (base+4)=(zeroBase base NL NR g m : ℤ) ∧ μ (base+5)=(next base NL NR g m : ℤ) ∧
    μ (base+6)=(NL : ℤ) ∧ μ (base+7)=(NR : ℤ) := by
  exact ⟨by simpa [header] using H.heads.getD (i := 0) (by simp [header]) 0,
    by simpa [header] using H.heads.getD (i := 1) (by simp [header]) 0,
    by simpa [header] using H.heads.getD (i := 2) (by simp [header]) 0,
    by simpa [header] using H.heads.getD (i := 3) (by simp [header]) 0,
    by simpa [header] using H.heads.getD (i := 4) (by simp [header]) 0,
    by simpa [header] using H.heads.getD (i := 5) (by simp [header]) 0,
    by simpa [header] using H.heads.getD (i := 6) (by simp [header]) 0,
    by simpa [header] using H.heads.getD (i := 7) (by simp [header]) 0⟩

end ThreeSum.SourceBandPairSlices

end

section


/-! # Concrete source inputs from the retained normalization and wanted outputs -/

namespace ThreeSum.SourceFiniteInputs

open Light GlobalEncoding LocalCoverBounds LightLocalCoverLayout LightLocalCoverSchedule

































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


/-! # Finite charge of the actual original-band histogram and bucket catalog -/

namespace ThreeSum.SourceBandCosts

open Scales TrimScales StageBounds CostLedger BandScales LocalCoverBounds

theorem choose_mul_le (L K N M : ℕ) : L.choose K*N.choose M ≤ (L+N).choose (K+M) := by
  rw [Nat.add_choose_eq]
  exact Finset.single_le_sum (f := fun ij : ℕ×ℕ => L.choose ij.1*N.choose ij.2)
    (fun _ _ => Nat.zero_le _) (by simp : (K,M) ∈ Finset.antidiagonal (K+M))

theorem choose_pow_le (L K J : ℕ) : (L.choose K)^J ≤ (J*L).choose (J*K) := by
  induction J with
  | zero => simp
  | succ J ih =>
    calc
      _ = (L.choose K)^J*L.choose K := pow_succ _ _
      _ ≤ (J*L).choose (J*K)*L.choose K := Nat.mul_le_mul_right _ ih
      _ ≤ (J*L+L).choose (J*K+K) := choose_mul_le _ _ _ _
      _ = _ := by simp only [Nat.succ_mul]

theorem typedOutputs_le_fullOutputs (n : ℕ) : typedOutputs n ≤ fullOutputs n := by
  have h := choose_pow_le (256*muZero n) (muZero n) (blockCount (inputBits n))
  have hwidth : blockCount (inputBits n)*(256*muZero n)=256*mu n := by
    unfold mu muZero totalSize
    ring
  have hcut : blockCount (inputBits n)*muZero n=mu n := rfl
  rw [hwidth,hcut] at h
  exact h

theorem four_le_scheduleSize (h : ℕ) : 4 ≤ GlobalEncoding.scheduleSize h := by
  unfold GlobalEncoding.scheduleSize LocalHashMoments.scheduleLength
  calc
    4 ≤ 320 := by decide
    _ ≤ 320*(2*h+1) := Nat.le_mul_of_pos_right _ (by omega)
    _ ≤ _ := Nat.le_mul_of_pos_right _ (by omega)

theorem localPrime_le_four_outputs (h : ℕ) : localPrime h ≤ 4*outputCount (512*h) h := by
  have ho : 2^(2*h) ≤ outputCount (512*h) h := by
    by_cases hz : h=0
    · simp [hz,outputCount]
    · exact (concrete_output_gt_pow (by omega)).le
  have hu := localPrime_sq_upper h
  have hm := Nat.mul_le_mul_left (16*outputCount (512*h) h) ho
  nlinarith

theorem modulus_le_global_outputs (h J : ℕ) :
    BlockSourceEncoding.modulus h J ≤ GlobalEncoding.scheduleSize h^J*
      (J*(512*h)).choose (J*(2*h)) := by
  have hl : localPrime h ≤ GlobalEncoding.scheduleSize h*outputCount (512*h) h :=
    (localPrime_le_four_outputs h).trans (Nat.mul_le_mul_right _ (four_le_scheduleSize h))
  have hp := Nat.pow_le_pow_left hl J
  rw [mul_pow] at hp
  unfold BlockSourceEncoding.modulus
  exact hp.trans (Nat.mul_le_mul_left _ (choose_pow_le (512*h) (2*h) J))

theorem modulus_le_tableCount (n : ℕ) :
    BlockSourceEncoding.modulus (microHalf (inputBits n)) (blockCount (inputBits n)) ≤ tableCount n := by
  have hm := modulus_le_global_outputs (microHalf (inputBits n)) (blockCount (inputBits n))
  have hc : blockCount (inputBits n)*(2*microHalf (inputBits n))=mu n := by
    rw [Nat.mul_comm,BlockSourceSharing.cutoff_eq]
  rw [BlockSourceSharing.width_eq,hc] at hm
  change LightBlockSourceCatalog.count (microHalf (inputBits n)) (blockCount (inputBits n))*fullOutputs n ≥ _ at hm
  rw [BlockSourceCatalogCosts.count_eq_scheduleCount] at hm
  exact hm

theorem bandSize_le_fullOutputs (n : ℕ) : bandSize n ≤ fullOutputs n := by
  have hb : bandSize n ≤ bandRoot n := by
    apply (ceilDiv_le_iff_le_mul (a := bandDivisor n) (bandDivisor_pos n)).mpr
    exact Nat.le_mul_of_pos_left _ (bandDivisor_pos n)
  have hr : bandRoot n ≤ typedOutputs n := by
    have hs := Nat.sqrt_le_self (typedOutputs n-1)
    have hp := typedOutputs_pos n
    unfold bandRoot rootCeiling
    omega
  exact hb.trans (hr.trans (typedOutputs_le_fullOutputs n))

theorem scheduleCount_pos (n : ℕ) : 0 < scheduleCount n := by
  unfold scheduleCount replicatedHalf
  exact pow_pos (localLength_pos _) _

theorem bands_outputs_le_encoderCount (n : ℕ) : bandCount n*fullOutputs n ≤ encoderCount n := by
  have hs : 1 ≤ scheduleCount n := scheduleCount_pos n
  calc
    _ ≤ bandCount n*scheduleCount n*fullOutputs n := by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_right (fullOutputs n) (Nat.mul_le_mul_left (bandCount n) hs)
    _ ≤ 2*(bandCount n*scheduleCount n*fullOutputs n) := Nat.le_mul_of_pos_left _ (by omega)
    _ = _ := by unfold encoderCount; ring

theorem input_le_encoderCount (n : ℕ) : n ≤ encoderCount n := by
  calc
    _ ≤ bandSize n*bandCount n := (bandCount_mul_bounds n).1
    _ ≤ fullOutputs n*bandCount n := Nat.mul_le_mul_right _ (bandSize_le_fullOutputs n)
    _ = bandCount n*fullOutputs n := Nat.mul_comm _ _
    _ ≤ _ := bands_outputs_le_encoderCount n

theorem bands_modulus_le_encoderCount (n : ℕ) :
    bandCount n*BlockSourceEncoding.modulus (microHalf (inputBits n)) (blockCount (inputBits n)) ≤ encoderCount n := by
  calc
    _ ≤ bandCount n*tableCount n := Nat.mul_le_mul_left _ (modulus_le_tableCount n)
    _ ≤ 2*(bandCount n*tableCount n) := Nat.le_mul_of_pos_left _ (by omega)
    _ = _ := by unfold tableCount encoderCount; ring

theorem bands_le_encoderCount (n : ℕ) : bandCount n ≤ encoderCount n := by
  calc
    _ ≤ bandCount n*BlockSourceEncoding.modulus (microHalf (inputBits n)) (blockCount (inputBits n)) :=
      Nat.le_mul_of_pos_right _ (BlockSourceEncoding.modulus_pos _ _)
    _ ≤ _ := bands_modulus_le_encoderCount n

theorem size_le_bandCount {N n : ℕ} (hN : N ≤ n) : BandPartition.size N (bandSize n) ≤ bandCount n := by
  apply (BandPartition.size_mono hN).trans
  by_cases hn : n=0
  · simp [hn,BandPartition.size]
  · have hg := bandSize_pos n
    have hb := (bandCount_mul_bounds n).1
    have hb' : n ≤ bandCount n*bandSize n := by simpa only [Nat.mul_comm] using hb
    have hd : (n-1)/bandSize n < bandCount n :=
      (Nat.div_lt_iff_lt_mul hg).mpr (by omega)
    simp only [BandPartition.size,if_neg hn]
    omega

















theorem persistent_space_le_encoderCount {base N n : ℕ} (hN : N ≤ n) :
    SourceBandLayout.work base N (bandSize n)
      (BlockSourceEncoding.modulus (microHalf (inputBits n)) (blockCount (inputBits n))) ≤
      base+14*encoderCount n := by
  have hs := SourceBandLayout.work_bound base N (bandSize n)
    (BlockSourceEncoding.modulus (microHalf (inputBits n)) (blockCount (inputBits n))) (bandSize_pos n)
  have hn := hN.trans (input_le_encoderCount n)
  have hb := size_le_bandCount hN
  have hm := (Nat.mul_le_mul_right
    (BlockSourceEncoding.modulus (microHalf (inputBits n)) (blockCount (inputBits n))) hb).trans
      (bands_modulus_le_encoderCount n)
  have hbc := hb.trans (bands_le_encoderCount n)
  nlinarith

end ThreeSum.SourceBandCosts

end

section


/-! # Finite cost of both actual original-band catalogs and empty padding -/

namespace ThreeSum.SourceBandPairCosts

open Scales TrimScales StageBounds CostLedger BandScales SourceBandPairData




















theorem tableCount_le_encoderCount {n : ℕ} (hn : 0 < n) : tableCount n ≤ encoderCount n := by
  have hb : 0 < bandCount n := by
    have hp := (bandCount_mul_bounds n).1
    by_contra h
    have hz : bandCount n=0 := by omega
    rw [hz,Nat.mul_zero] at hp
    omega
  calc
    _ ≤ bandCount n*tableCount n := Nat.le_mul_of_pos_left _ hb
    _ ≤ 2*(bandCount n*tableCount n) := Nat.le_mul_of_pos_left _ (by omega)
    _ = _ := by unfold tableCount encoderCount; ring

theorem modulus_le_encoderCount {n : ℕ} (hn : 0 < n) :
    BlockSourceEncoding.modulus (microHalf (inputBits n)) (blockCount (inputBits n)) ≤ encoderCount n :=
  (SourceBandCosts.modulus_le_tableCount n).trans (tableCount_le_encoderCount hn)











theorem next_le_encoderCount {base NL NR n : ℕ} (hn : 0 < n) (hNL : NL ≤ n) (hNR : NR ≤ n) :
    next base NL NR (bandSize n)
      (BlockSourceEncoding.modulus (microHalf (inputBits n)) (blockCount (inputBits n))) ≤
      base+29*encoderCount n+9 := by
  have hl := SourceBandCosts.persistent_space_le_encoderCount (base := leftBase base) hNL
  have hr := SourceBandCosts.persistent_space_le_encoderCount
    (base := rightBase base NL (bandSize n)
      (BlockSourceEncoding.modulus (microHalf (inputBits n)) (blockCount (inputBits n)))) hNR
  have hm := modulus_le_encoderCount hn
  change rightBase base NL (bandSize n) _ ≤ _ at hl
  change zeroBase base NL NR (bandSize n) _ ≤ _ at hr
  unfold next leftBase at *
  omega

end ThreeSum.SourceBandPairCosts

end

section


/-! # Exact shared construction counts and finite encoder charge -/

namespace ThreeSum.SourceBandBanksCosts

open Scales TrimScales StageBounds CostLedger BandScales SubsetAddress














theorem count_le_bandCount {NL NR n : ℕ} (hNL : NL ≤ n) (hNR : NR ≤ n) :
    SourceBandPairSlices.count NL NR (bandSize n) ≤ bandCount n :=
  max_le (SourceBandCosts.size_le_bandCount hNL) (SourceBandCosts.size_le_bandCount hNR)





































































theorem finish_eq (base NL NR g h J cut : ℕ) :
    SourceBandBankData.finish base NL NR g h J cut=
      base+5+SourceBandPairSlices.count NL NR g*SourceBandBankLayout.span h J cut := rfl








































theorem finish_le_encoderCount {base NL NR n : ℕ} (hNL : NL ≤ n) (hNR : NR ≤ n) :
    SourceBandBankData.finish base NL NR (bandSize n) (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n) ≤
      base+5+storageFactor n*encoderCount n := by
  rw [finish_eq]
  exact Nat.add_le_add_left (span_count_le_encoderCount (count_le_bandCount hNL hNR)) _











end ThreeSum.SourceBandBanksCosts

end

section


/-! # Finite resource charge of the actual original-array source host -/

namespace ThreeSum.SourceBandHostCosts

open Scales TrimScales StageBounds CostLedger BandScales











theorem scheduleCount_le_encoderCount {n : ℕ} (hn : 0 < n) : scheduleCount n ≤ encoderCount n := by
  have hf : 0 < fullOutputs n :=
    (typedOutputs_pos n).trans_le (SourceBandCosts.typedOutputs_le_fullOutputs n)
  have hs : scheduleCount n ≤ tableCount n := Nat.le_mul_of_pos_right _ hf
  exact hs.trans (SourceBandPairCosts.tableCount_le_encoderCount hn)

theorem occurrenceRows_le_encoderCount {n : ℕ} (hn : 0 < n) :
    LightBlockSourceCatalog.count (microHalf (inputBits n)) (blockCount (inputBits n))*blockCount (inputBits n) ≤
      blockCount (inputBits n)*encoderCount n := by
  rw [BlockSourceCatalogCosts.count_eq_scheduleCount]
  have h := Nat.mul_le_mul_right (blockCount (inputBits n)) (scheduleCount_le_encoderCount hn)
  simpa only [Nat.mul_comm] using h

theorem bankHeader_le_encoderCount {base NL NR n : ℕ} (hn : 0 < n) (hNL : NL ≤ n) (hNR : NR ≤ n) :
    LightSourceBandHost.bankHeader base NL NR (bandSize n)
      (microHalf (inputBits n)) (blockCount (inputBits n)) ≤
      base+(29+blockCount (inputBits n))*encoderCount n+9 := by
  have hp := SourceBandPairCosts.next_le_encoderCount (base := base) hn hNL hNR
  have hr := occurrenceRows_le_encoderCount hn
  unfold LightSourceBandHost.bankHeader LightSourceBandHost.occurrenceBase
  nlinarith

theorem finish_le_encoderCount {base NL NR n : ℕ} (hn : 0 < n) (hNL : NL ≤ n) (hNR : NR ≤ n) :
    LightSourceBandHost.finish base NL NR (bandSize n)
      (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n) ≤
      base+(29+blockCount (inputBits n)+SourceBandBanksCosts.storageFactor n)*encoderCount n+14 := by
  have hh := bankHeader_le_encoderCount (base := base) hn hNL hNR
  have hb := SourceBandBanksCosts.finish_le_encoderCount
    (base := LightSourceBandHost.bankHeader base NL NR (bandSize n)
      (microHalf (inputBits n)) (blockCount (inputBits n))) hNL hNR
  unfold LightSourceBandHost.finish
  nlinarith



















end ThreeSum.SourceBandHostCosts

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

theorem incidences_length_le {A B C : List ℤ} {n : ℕ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (ha : A.length ≤ n) (hb : B.length ≤ n) (hc : C.length ≤ n) :
    (incidences n A B C hsA hsB hsC).length ≤ bandSize n*ColorBandBounds.count n (bandSize n) := by
  unfold incidences
  rw [values_length]
  exact (items_length_le ..).trans (Nat.mul_le_mul_left _ (records_length_le ha hb hc))

theorem incidences_bounded {A B C : List ℤ} {n U : ℕ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (hA : ∀ j < A.length, |A.getD j 0| ≤ (U : ℤ)) :
    ∀ z ∈ incidences n A B C hsA hsB hsC, |z| ≤ (U : ℤ) := values_bounded hA

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


/-! # Keep the complete finite source catalog below its exact returned end -/

namespace ThreeSum.SourceFiniteData

open Light

theorem source_ends (base NL NR g h J cut : ℕ) :
    base+3 ≤ LightSourceControlsHost.finish base NL NR g h J cut ∧
    SourceBandPairData.next (LightSourceControlsHost.sourceBase base) NL NR g
      (BlockSourceEncoding.modulus h J) ≤ LightSourceControlsHost.finish base NL NR g h J cut ∧
    LightSourceBandHost.bankHeader (LightSourceControlsHost.sourceBase base) NL NR g h J+5 ≤
      LightSourceControlsHost.finish base NL NR g h J cut := by
  have ho := SourceBandPairData.ordered (LightSourceControlsHost.sourceBase base)
    NL NR g (BlockSourceEncoding.modulus h J)
  unfold LightSourceControlsHost.finish LightSourceBandHost.finish SourceBandBankData.finish
    SourceBandBankLayout.baseAt SourceBandBankData.first LightSourceBandHost.bankHeader
    LightSourceBandHost.occurrenceBase LightSourceControlsHost.sourceBase
  unfold SourceBandPairData.leftBase LightSourceControlsHost.sourceBase at ho
  omega

theorem Stored.of_kept {μ ν : ℕ → ℤ} {base g p h J cut bound : ℕ} {B C : List ℤ} {shift r : ℤ}
    (H : Stored μ base g p h J cut B C shift r)
    (K : Kept μ ν bound)
    (hb : LightSourceControlsHost.finish base B.length C.length g h J cut ≤ bound) :
    Stored ν base g p h J cut B C shift r := by
  obtain ⟨hcontrol,hpair,_⟩ := source_ends base B.length C.length g h J cut
  refine ⟨H.returned,?_,?_,?_⟩
  · exact H.controls.of_kept K (by simpa [SourceControlLayout.values] using hcontrol.trans hb)
  · exact H.buckets.of_kept (BlockSourceEncoding.modulus_pos h J) K (hpair.trans hb)
  · exact H.banks.of_kept K le_rfl hb

end ThreeSum.SourceFiniteData

end

section


/-! # Exact reusable memory boundary after the actual wanted-pair output -/

namespace ThreeSum.EncodedColorWantedData

open Light WantedResidueKeys




theorem header_le_nextFree (out M : ℕ) (left right : ℕ → ℤ) (NL NR : ℕ) (shift : ℤ) :
    out+4 ≤ nextFree out M left right NL NR shift := by
  unfold nextFree LightWantedSetup.pairBase LightSourceBucketSetup.next LightWantedSetup.bucketBase
    LightWantedSetup.rightCodes LightWantedSetup.leftCodes
  omega





theorem of_kept {μ ν : ℕ → ℤ} {out M NL NR bound : ℕ} {left right : ℕ → ℤ} {shift : ℤ}
    (H : LightWantedSetup.Output μ out M left right NL NR shift)
    (K : Kept μ ν bound) (hb : nextFree out M left right NL NR shift ≤ bound) :
    LightWantedSetup.Output ν out M left right NL NR shift := by
  have hh := (header_le_nextFree out M left right NL NR shift).trans hb
  obtain ⟨hcount,hpair,hnext,hshift,ps,hlen,hnodup,hmem,hrows⟩ := H
  refine ⟨(K _ (by omega)).trans hcount,(K _ (by omega)).trans hpair,
    (K _ (by omega)).trans hnext,(K _ (by omega)).trans hshift,ps,hlen,hnodup,hmem,?_⟩
  apply hrows.of_kept K
  rw [WantedPairs.cells_length,hlen]
  exact hb

end ThreeSum.EncodedColorWantedData

end

section


/-! # Finite cost of computed source controls and their full host -/

namespace ThreeSum.SourceControlCosts

open Scales TrimScales StageBounds CostLedger BandScales











































theorem finish_le_encoderCount {base NL NR n : ℕ} (hn : 0 < n) (hNL : NL ≤ n) (hNR : NR ≤ n) :
    LightSourceControlsHost.finish base NL NR (bandSize n)
      (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n) ≤
      base+(29+blockCount (inputBits n)+SourceBandBanksCosts.storageFactor n)*encoderCount n+17 := by
  have hs := SourceBandHostCosts.finish_le_encoderCount (base := base+3) hn hNL hNR
  unfold LightSourceControlsHost.finish LightSourceControlsHost.sourceBase
  omega




















end ThreeSum.SourceControlCosts

end

section


/-! # Uniform original-size budgets for the finite normalized source host -/

namespace ThreeSum.SourceFiniteCosts

open Scales TrimScales StageBounds CostLedger BandScales





































theorem finish_le {base NL NR n : ℕ} (hn : 0 < n) (hNL : NL ≤ n) (hNR : NR ≤ n) :
    LightSourceControlsHost.finish base NL NR (bandSize n)
      (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n) ≤ finish base n :=
  SourceControlCosts.finish_le_encoderCount hn hNL hNR






end ThreeSum.SourceFiniteCosts

end

section


/-! # Numeric envelopes for the actually balanced wanted records -/

namespace ThreeSum.EncodedColorWantedCosts

open Light WantedResidueKeys

set_option maxHeartbeats 1800000

























theorem time_le (P M h J U : ℕ) [NeZero M] (xs : List ℤ) :
    LightGuardedWanted.time P M h J U xs ≤ time P M h J U xs.length := by
  have h := LightBalancedWanted.time_bound M (LightGuardedWanted.left P xs)
    (LightGuardedWanted.right h J) (3*xs.length) (LightGuardedWanted.totalKeys h J)
    (LightGuardedWanted.keyBound P h J)
  unfold LightGuardedWanted.time time
  omega

theorem sourceBase_eq (free M h J len : ℕ) :
    sourceBase free M h J len=LightCoverKeyData.keyEnd free h J+
      6*len+2*LightGuardedWanted.totalKeys h J+3*M+5+
      2*(3*len*LightGuardedWanted.totalKeys h J/M) := by
  unfold sourceBase LightWantedSetup.pairBase LightSourceBucketSetup.next LightWantedSetup.bucketBase
    LightWantedSetup.rightCodes LightWantedSetup.leftCodes LightGuardedWanted.wantedFree
  omega

theorem sourceBase_le (free P M h J : ℕ) [NeZero M] (xs : List ℤ) :
    EncodedColorWantedData.nextFree (LightGuardedWanted.wantedFree free h J xs.length) M
      (LightGuardedWanted.left P xs) (LightGuardedWanted.right h J)
      (3*xs.length) (LightGuardedWanted.totalKeys h J) (RawAKeyLists.selected M P xs h J) ≤
        sourceBase free M h J xs.length := by
  have h := LightBalancedWanted.total_le_div M (LightGuardedWanted.left P xs)
    (LightGuardedWanted.right h J) (3*xs.length) (LightGuardedWanted.totalKeys h J)
  rw [LightGuardedWanted.selected_eq] at h
  unfold EncodedColorWantedData.nextFree sourceBase
  exact Nat.add_le_add_left (Nat.mul_le_mul_left 2 h) _

theorem space_le (free P M h J U : ℕ) [NeZero M] (xs : List ℤ) :
    LightGuardedWanted.space free P M h J U xs ≤ space free P M h J U xs.length := by
  have h := sourceBase_le free P M h J xs
  unfold LightGuardedWanted.space LightBalancedWanted.space LightWantedSetup.space space
  rw [LightGuardedWanted.selected_eq]
  exact max_le_max le_rfl (max_le_max le_rfl (max_le_max le_rfl (max_le_max le_rfl h)))

theorem keyBound_mono {P P' h J : ℕ} (hP : P ≤ P') :
    LightGuardedWanted.keyBound P h J ≤ LightGuardedWanted.keyBound P' h J := by
  unfold LightGuardedWanted.keyBound
  omega

theorem sourceBase_mono {free M h J len len' : ℕ} (hlen : len ≤ len') :
    sourceBase free M h J len ≤ sourceBase free M h J len' := by
  rw [sourceBase_eq,sourceBase_eq]
  gcongr

theorem time_mono {P P' M h J U len len' : ℕ} (hP : P ≤ P') (hlen : len ≤ len') :
    time P M h J U len ≤ time P' M h J U len' := by
  have hkey := keyBound_mono (h := h) (J := J) hP
  unfold time LightRawAKeys.time LightOriginalOffset.time LightResidueHistogram.time
    LightResidues.residuesTime LightResidues.residueBudget LightHistogram.histogramTime
    LightHistogram.countTime LightReportingAffine.time
  gcongr

theorem space_mono {free P P' M h J U len len' : ℕ} (hP : P ≤ P') (hlen : len ≤ len') :
    space free P M h J U len ≤ space free P' M h J U len' := by
  have hkey := keyBound_mono (h := h) (J := J) hP
  have hbase := sourceBase_mono (free := free) (M := M) (h := h) (J := J) hlen
  unfold space LightRawAKeys.space LightOriginalOffset.space LightSourceResidues.space
    LightWantedSetup.pairBase LightSourceBucketSetup.next LightWantedSetup.bucketBase
    LightWantedSetup.rightCodes LightWantedSetup.leftCodes LightGuardedWanted.wantedFree
  gcongr

theorem word_mono {P P' M h J U len len' : ℕ} (hP : P ≤ P') (hlen : len ≤ len') :
    LightGuardedWanted.word P M h J U len ≤ LightGuardedWanted.word P' M h J U len' := by
  have hkey := keyBound_mono (h := h) (J := J) hP
  unfold LightGuardedWanted.word LightRawAKeys.word LightBalancedWanted.word
    LightOriginalOffset.word LightKaratsuba.wordBound LightSourceResidues.word
  gcongr

end ThreeSum.EncodedColorWantedCosts

end

section


/-! # Uniform budgets for wanted records followed by the shared source banks -/

namespace ThreeSum.EncodedColorStageCosts

open Scales BandScales ArithmeticStageBounds



















theorem source_time_mono {n p P U D : ℕ} (hp : p ≤ P) :
    EncodedColorSourcesCosts.time n p U D ≤ EncodedColorSourcesCosts.time n P U D := by
  unfold EncodedColorSourcesCosts.time SourceFiniteCosts.time
  gcongr

theorem source_space_mono {base bound n p P U D : ℕ} (hb : base ≤ bound) (hp : p ≤ P) :
    SourceFiniteCosts.space base n p U D ≤ SourceFiniteCosts.space bound n P U D := by
  unfold SourceFiniteCosts.space
  gcongr

theorem source_word_mono {n p P U D : ℕ} (hp : p ≤ P) :
    SourceFiniteCosts.word n p U D ≤ SourceFiniteCosts.word n P U D := by
  unfold SourceFiniteCosts.word LightSourceControlsHost.word LightSourceBandHost.word
    LightSourceBandPair.word LightSourceBandStep.word LightSourceResidues.word
  gcongr

theorem base_le {free n p M len : ℕ} [NeZero M] {xs : List ℤ} (hlen : xs.length ≤ len) :
    LightEncodedColorFiniteSources.base free n p M xs ≤ sourceBase free n M len :=
  (EncodedColorWantedCosts.sourceBase_le free p M (microHalf (inputBits n))
    (blockCount (inputBits n)) xs).trans (EncodedColorWantedCosts.sourceBase_mono hlen)

theorem time_le {n p P M U len : ℕ} [NeZero M] {xs : List ℤ}
    (hp : p ≤ P) (hlen : xs.length ≤ len) :
    LightEncodedColorWantedSources.time n p M U xs ≤ time n P M U len := by
  have hw := (EncodedColorWantedCosts.time_le p M (microHalf (inputBits n))
    (blockCount (inputBits n)) U xs).trans (EncodedColorWantedCosts.time_mono hp hlen)
  have hs := source_time_mono (n := n) (U := U) (D := M) hp
  unfold LightEncodedColorWantedSources.time time
  omega

theorem space_le {free n p P M U len : ℕ} [NeZero M] {xs : List ℤ}
    (hp : p ≤ P) (hlen : xs.length ≤ len) :
    LightEncodedColorWantedSources.space free n p M U xs ≤ space free n P M U len := by
  have hw := (EncodedColorWantedCosts.space_le free p M (microHalf (inputBits n))
    (blockCount (inputBits n)) U xs).trans (EncodedColorWantedCosts.space_mono hp hlen)
  exact max_le_max hw (source_space_mono (base_le hlen) hp)

theorem word_le {n p P M U len len' : ℕ} (hp : p ≤ P) (hlen : len ≤ len') :
    LightEncodedColorWantedSources.word n p M U len ≤ word n P M U len' :=
  max_le_max (EncodedColorWantedCosts.word_mono hp hlen) (source_word_mono hp)

theorem depth_le {n M len len' : ℕ} (hlen : len ≤ len') :
    LightEncodedColorWantedSources.depth n M len ≤ depth n M len' := by
  unfold depth LightEncodedColorWantedSources.depth
  omega

theorem finish_le {base bound NL NR n : ℕ} (hn : 0 < n)
    (hb : base ≤ bound) (hNL : NL ≤ n) (hNR : NR ≤ n) :
    LightSourceControlsHost.finish base NL NR (bandSize n)
      (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n) ≤ SourceFiniteCosts.finish bound n := by
  apply (SourceFiniteCosts.finish_le hn hNL hNR).trans
  unfold SourceFiniteCosts.finish
  omega

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


/-! # Execute one original color through the retained shared source bank -/

namespace ThreeSum.LightEncodedColorPipeline

open Light Scales BandScales ArithmeticStageBounds ColorClassLists EncodedColorLayout
open EncodedColorNormalizedData

set_option maxHeartbeats 4200000
set_option maxRecDepth 17000

local instance (n : ℕ) : NeZero (radix n) := ⟨Nat.ne_of_gt (radix_pos n)⟩























































variable {lim : Limits} {d : ℕ}

theorem program_meets_sourceProof {μ : ℕ → ℤ} {src n params row free U : ℕ}
    (color : Coloring.Parameter (inputBits n+1)) (x : Fin n → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hn : 0 < n) (hR : 4 ≤ radix n)
    (hsrc : src+n ≤ free) (hparams : params+19 ≤ free) (hrow : row+6 ≤ free)
    (hspace : space free n U ≤ lim.space) (hword : (word n U : ℤ) ≤ lim.word)
    (hd : d+depth n ≤ lim.depth)
    (hread : Seg μ src (List.ofFn x)) (hbound : ∀ i, |x i| ≤ (U : ℤ))
    (hparameters : Seg μ params (LightParameterInit.values n))
    (hcolor : Seg μ row (ColorParameters.fields color)) :
    Meets lim program 255 d [src,n,params,row,free] μ (time n U)
      (fun r ν => EncodedColorPipelineData.Output ν free n color x r ∧ Kept μ ν free) := by
  have hsPrime : LightEncodedColorPrimeHost.inputSpace free n U ≤ lim.space := (le_max_left _ _).trans hspace
  have hsStage : EncodedColorStageCosts.space (EncodedColorPipelineData.coverBase free n) n (maxMod n)
      (radix n) U (EncodedColorStageCosts.incidenceCap n) ≤ lim.space :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hspace)
  have hsFinish : finishBound free n+8 ≤ lim.space := (le_max_right _ _).trans ((le_max_right _ _).trans hspace)
  have hsmall (a : ℕ) (ha : a ≤ word n U) : (a : ℤ) ≤ lim.word := (Int.ofNat_le.mpr ha).trans hword
  have hwPrime := hsmall (LightEncodedColorPrimeHost.inputWord n U) (by unfold word; omega)
  have hwStage := hsmall (EncodedColorStageCosts.word n (maxMod n) (radix n) U
    (EncodedColorStageCosts.incidenceCap n)) (by unfold word; omega)
  have hCapWord := hsmall (EncodedColorStageCosts.incidenceCap n) (by unfold word; omega)
  have hPWord := hsmall (maxMod n) (by unfold word; omega)
  have hMWord := hsmall (radix n) (by unfold word; omega)
  have hGWord := hsmall (bandSize n) (by unfold word; omega)
  have hHWord := hsmall (microHalf (inputBits n)) (by unfold word; omega)
  have hJWord := hsmall (blockCount (inputBits n)) (by unfold word; omega)
  have hCutWord := hsmall (mu n) (by unfold word; omega)
  have hSWord := hsmall (LightBlockSourceCatalog.count (microHalf (inputBits n)) (blockCount (inputBits n)))
    (by unfold word; omega)
  have hdPrime : d+1+LightEncodedColorPrimeHost.depth n ≤ lim.depth := by unfold depth at hd; omega
  have hdStage : d+1+EncodedColorStageCosts.depth n (radix n) (EncodedColorStageCosts.incidenceCap n) ≤
      lim.depth := by unfold depth at hd; omega
  have add2 : ((free : ℤ)+2).toNat=free+2 := by omega
  have add3 : ((free : ℤ)+3).toNat=free+3 := by omega
  have add4 : ((free : ℤ)+4).toNat=free+4 := by omega
  have add5 : ((free : ℤ)+5).toNat=free+5 := by omega
  have add7 : ((free : ℤ)+7).toNat=free+7 := by omega
  have par1 : ((params : ℤ)+1).toNat=params+1 := by omega
  have par3 : ((params : ℤ)+3).toNat=params+3 := by omega
  have par4 : ((params : ℤ)+4).toNat=params+4 := by omega
  have par14 : ((params : ℤ)+14).toNat=params+14 := by omega
  have par17 : ((params : ℤ)+17).toNat=params+17 := by omega
  have prime2 : ((prime free n (bandSize n) : ℤ)+2).toNat=prime free n (bandSize n)+2 := by omega
  have primePrev : ((prime free n (bandSize n) : ℤ)-1).toNat=normalizedEnd free n (bandSize n) := by
    unfold prime
    omega
  apply Meets.of_body (p := 255) (by rfl : program[255]?=some (body 71 252 253 254))
  unfold body time
  have hPrime := ((LightEncodedColorPrimeHost.program_meets_input (d := d+1) (μ := μ)
    (src := src) (params := params) (row := row) (free := free)
    color x hw hn hR hsrc hparams hrow hsPrime hwPrime hdPrime hread hbound hparameters hcolor).append
      (LightEncodedColorWantedSources.program.map (ReportingHostRelocation.relocate 72))).append
      [LightEncodedColorWantedHeader.body,LightEncodedColorResult.body,body 71 252 253 254]
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
      | refine Light.Ends.callToThen (hPrime _ (by omega)) ?_ ?_ ?_ ?_
      | refine Light.Ends.callToThen hPrime ?_ ?_ ?_ ?_);
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
        ((rintro ptr μ₁
              ⟨hptr, ⟨heads, A, hsA, B, hsB, C, hsC, hcount, normalized, primes⟩,
                  keptPrime⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  let xs := incidences n A B C hsA hsB hsC
  let p := EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC
  let cover := EncodedColorPipelineData.coverBase free n
  let wanted := EncodedColorPipelineData.wantedHeader free n xs.length
  let base := EncodedColorPipelineData.controls free n A B C hsA hsB hsC
  let bank := EncodedColorPipelineData.bankHeader free n A B C hsA hsB hsC
  let finish := EncodedColorPipelineData.finish free n A B C hsA hsB hsC
  let occ := LightSourceBandHost.occurrenceBase (LightSourceControlsHost.sourceBase base)
    B.length C.length (bandSize n) (microHalf (inputBits n)) (blockCount (inputBits n))
  have ha := length_classList_le color x 0 1
  have hb := length_classList_le color x 1 1
  have hc := length_classList_le color x 2 (-1)
  have hnA := normalized.2.1.2.1.trans ha
  have hnB := normalized.2.2.1.2.1.trans hb
  have hnC := normalized.2.2.2.1.2.1.trans hc
  have hlen : xs.length ≤ EncodedColorStageCosts.incidenceCap n := incidences_length_le hnA hnB hnC
  have hp : 0 < p := EncodedColorPrimeReadyData.selected_pos
  have hmax : p ≤ maxMod n := EncodedColorStageCosts.selected_le_maxMod hR
  have hbaseBound : base ≤ sourceBound free n := EncodedColorStageCosts.base_le hlen
  have hfinishBound : finish ≤ finishBound free n := EncodedColorStageCosts.finish_le hn hbaseBound hnB hnC
  have hfinishSpace : finish+8 ≤ lim.space := by omega
  obtain ⟨hmeta,hfree,hcover,hwanted,hcontrol,hbank⟩ := EncodedColorPipelineData.ordered free n A B C hsA hsB hsC
  change prime free n (bandSize n)+6 ≤ cover at hmeta
  change free+8 ≤ cover at hfree
  change cover ≤ base at hcover
  change wanted+4 ≤ base at hwanted
  change base+3 ≤ finish at hcontrol
  change bank+5 ≤ finish at hbank
  obtain ⟨hav,hae,hbv,hbe,hcv,hce,htables,hrecords,hcatalog⟩ :=
    normalized_ends_cover free n (bandSize n) (radix n) (primeWindow n)
  change av free n+n ≤ cover at hav
  change ae free n+2+2*n ≤ cover at hae
  change bv free n+n ≤ cover at hbv
  change be free n+2+2*n ≤ cover at hbe
  change cv free n+n ≤ cover at hcv
  change ce free n+2+2*n ≤ cover at hce
  change tables free n+ColorBandBounds.count n (bandSize n) ≤ cover at htables
  change rec free n (bandSize n)+4*ColorBandBounds.count n (bandSize n) ≤ cover at hrecords
  change normalizedEnd free n (bandSize n) ≤ cover at hcatalog
  have hvals : vals free n (bandSize n)+xs.length ≤ cover := by
    have hle : vals free n (bandSize n)+xs.length ≤ normalizedEnd free n (bandSize n) := by
      unfold EncodedColorStageCosts.incidenceCap at hlen
      unfold normalizedEnd LightBandRawA.space LightBandRawA.positionBase LightBandRawA.ownerBase LightBandRawA.capacity
      omega
    exact hle.trans hcatalog
  have hActualSpace := (EncodedColorStageCosts.space_le (free := cover) (U := U) hmax hlen).trans hsStage
  have hActualWord := (Int.ofNat_le.mpr (EncodedColorStageCosts.word_le (U := U) hmax hlen)).trans hwStage
  have hActualDepth : d+1+LightEncodedColorWantedSources.depth n (radix n) xs.length ≤ lim.depth :=
    (Nat.add_le_add_left (EncodedColorStageCosts.depth_le hlen) (d+1)).trans hdStage
  obtain ⟨readP,_,readCover,_,_,_⟩ := primes.heads_read
  change μ₁ (prime free n (bandSize n))=(p : ℤ) at readP
  change μ₁ (prime free n (bandSize n)+2)=(cover : ℤ) at readCover
  obtain ⟨_,_,readB,readBE,readC,readCE,_,readVals⟩ := EncodedColorNormalizedData.heads_read heads
  have params₁ := hparameters.of_kept keptPrime (by
    simpa [LightParameterInit.values,LightScales.values,LightLocalParameters.values,LightLocalCounts.values,
      LightGlobalSizes.values] using hparams)
  obtain ⟨_,readH,readJ,readCut,readM,readG,_⟩ := EncodedColorParameterData.reads params₁
  have hlenWord : (xs.length : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hlen).trans hCapWord
  have hpWord : (p : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hmax).trans hPWord
  have hPrevEq : (prime free n (bandSize n) : ℤ)-1=(normalizedEnd free n (bandSize n) : ℤ) := by
    unfold prime
    omega
  have hPrevWord : (normalizedEnd free n (bandSize n) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (show normalizedEnd free n (bandSize n) ≤ lim.space by omega)).trans hw
  change μ₁ (normalizedEnd free n (bandSize n))=(xs.length : ℤ) at hcount
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
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hptr,
                readP]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hptr, readP] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hptr, readP] <;> omega)));
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
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hptr,
                prime2, readCover]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hptr, prime2, readCover] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hptr, prime2, readCover] <;>
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
    (refine Light.Ends.setToThen (xs.length : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hptr,
                hPrevEq, hcount]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hptr, hPrevEq, hcount] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hptr, hPrevEq, hcount] <;>
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
    (refine Light.Ends.setToThen (vals free n (bandSize n) : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                readVals, add7]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [readVals, add7] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, readVals, add7] <;>
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
    (refine Light.Ends.setToThen (bv free n : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, readB,
                add2]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [readB, add2] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, readB, add2] <;> omega)));
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
    (refine Light.Ends.setToThen (be free n : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, readBE,
                add3]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [readBE, add3] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, readBE, add3] <;> omega)));
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
    (refine Light.Ends.setToThen (cv free n : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, readC,
                add4]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [readC, add4] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, readC, add4] <;> omega)));
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
    (refine Light.Ends.setToThen (ce free n : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, readCE,
                add5]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [readCE, add5] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, readCE, add5] <;> omega)));
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
    (refine Light.Ends.setToThen (microHalf (inputBits n) : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, readH,
                par1]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [readH, par1] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, readH, par1] <;> omega)));
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
    (refine Light.Ends.setToThen (blockCount (inputBits n) : ℕ) ?_ ?_ ?_);
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
    (refine Light.Ends.setToThen (mu n : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, readCut,
                par4]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [readCut, par4] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, readCut, par4] <;> omega)));
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
    (refine Light.Ends.setToThen (radix n : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, readM,
                par14]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [readM, par14] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, readM, par14] <;> omega)));
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
    (refine Light.Ends.setToThen (bandSize n : ℕ) ?_ ?_ ?_);
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
  have hxs : Seg μ₁ (vals free n (bandSize n)) xs := normalized.2.2.2.2.2.2.valueRows
  have hclassA := LightColorBands.class_bounded color x 0 1 (by norm_num) hbound
  have hclassB := LightColorBands.class_bounded color x 1 1 (by norm_num) hbound
  have hclassC := LightColorBands.class_bounded color x 2 (-1) (by norm_num) hbound
  have hxsBound : ∀ z ∈ xs, |z| ≤ (U : ℤ) :=
    incidences_bounded (SourceFiniteInputs.prepared_bound normalized.2.1 hclassA)
  have hSources := (ReportingHostRelocation.meets
    (LightEncodedColorWantedSources.program_meets (d := d+1) (μ := μ₁) (a := vals free n (bandSize n))
      (free := cover) (p := p) (M := radix n) (U := U) (xs := xs) hw hActualDepth hn hp ha hb hc hvals
      hav hae hbv hbe hcv hce htables hrecords hcatalog hActualSpace hActualWord hxs hxsBound
      hclassB hclassC normalized) LightEncodedColorPrimeHost.program).append
      [LightEncodedColorWantedHeader.body,LightEncodedColorResult.body,body 71 252 253 254]
  have hSourcesBound := hSources.mono_time (EncodedColorStageCosts.time_le hmax hlen)
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
      | refine Light.Ends.callToThen (hSourcesBound _ (by omega)) ?_ ?_ ?_ ?_
      | refine Light.Ends.callToThen hSourcesBound ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                LightEncodedColorWantedSources.args]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [LightEncodedColorWantedSources.args] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul,
                LightEncodedColorWantedSources.args] <;>
              omega)));
    (on_goal -1 =>
        ((rintro last μ₂
              ⟨normalized₂, sources, cover₂, wanted₂, countBound, lifts,
                  keptSources⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  have hlast : last=(finish : ℤ) := sources.returned
  have hnext : μ₂ (wanted+2)=(base : ℤ) := wanted₂.2.2.1
  have readOcc : μ₂ (base+8)=(occ : ℤ) := by
    simpa [LightSourceControlsHost.sourceBase,Nat.add_assoc,occ,LightSourceBandHost.occurrenceBase,
      base,EncodedColorPipelineData.controls,cover,p,xs]
      using (SourceBandPairSlices.heads_read sources.buckets).2.2.2.2.2.1
  have readS : μ₂ (base+1)=(LightBlockSourceCatalog.count (microHalf (inputBits n)) (blockCount (inputBits n)) : ℤ) := by
    simpa [SourceControlLayout.values,base,EncodedColorPipelineData.controls,cover,p,xs]
      using sources.controls.getD (i := 1) (by simp [SourceControlLayout.values]) 0
  have hbankEq : bank=occ+LightBlockSourceCatalog.count (microHalf (inputBits n)) (blockCount (inputBits n))*
      blockCount (inputBits n) := rfl
  have hHeader := LightEncodedColorWantedHeader.meets (d := d+1) (μ := μ₂)
    (by rfl : program[253]?=some LightEncodedColorWantedHeader.body) hw (by change wanted ≤ lim.space; omega) cover₂
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
      | refine Light.Ends.callToThen (hHeader _ (by omega)) ?_ ?_ ?_ ?_
      | refine Light.Ends.callToThen hHeader ?_ ?_ ?_ ?_);
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
        ((rintro out μ₃ ⟨hout, hmem⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  subst μ₃
  have hout' : out=(wanted : ℤ) := hout
  have wanted2 : ((wanted : ℤ)+2).toNat=wanted+2 := by omega
  have base1 : ((base : ℤ)+1).toNat=base+1 := by omega
  have base8 : ((base : ℤ)+8).toNat=base+8 := by omega
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (base : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hout',
                wanted2, hnext]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hout', wanted2, hnext] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hout', wanted2, hnext] <;>
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
    (refine Light.Ends.setToThen (occ : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, base8,
                readOcc]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [base8, readOcc] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, base8, readOcc] <;>
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
    (refine
        Light.Ends.setToThen
          (LightBlockSourceCatalog.count (microHalf (inputBits n))
              (blockCount (inputBits n)) :
            ℕ)
          ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, base1,
                readS]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [base1, readS] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, base1, readS] <;> omega)));
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
    (refine Light.Ends.setToThen (bank : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                hbankEq]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hbankEq] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hbankEq] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  have hResult := LightEncodedColorResult.meets (d := d+1) (μ := μ₂)
    (prime := prime free n (bandSize n)) (cover := cover) (wanted := wanted) (controls := base) (bank := bank)
    (out := finish) (len := xs.length) (p := p)
    (by rfl : program[254]?=some LightEncodedColorResult.body) hw (by omega) (by omega) (by omega)
    (by omega) (by omega) hfinishSpace hlenWord hpWord
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
      | refine Light.Ends.callToThen (hResult _ (by omega)) ?_ ?_ ?_ ?_
      | refine Light.Ends.callToThen hResult ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hptr,
                hout', hlast]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hptr, hout', hlast] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hptr, hout', hlast] <;>
              omega)));
    (on_goal -1 =>
        ((rintro r ν ⟨hr, finalHeads, keptResult⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  have primes₂ := primes.of_kept keptSources le_rfl
  have heads₂ := heads.of_kept keptSources (by simpa [normalizedHeads] using hfree)
  have count₂ : μ₂ (normalizedEnd free n (bandSize n))=(xs.length : ℤ) :=
    (keptSources _ (by unfold prime at hmeta; omega)).trans hcount
  have hkeyEnd : LightCoverKeyData.keyEnd cover (microHalf (inputBits n)) (blockCount (inputBits n)) ≤ finish := by
    have hh : wanted=LightCoverKeyData.keyEnd cover (microHalf (inputBits n)) (blockCount (inputBits n))+3*xs.length := rfl
    omega
  refine ⟨⟨A,hsA,B,hsB,C,hsC,hr,⟨finalHeads,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩⟩,?_⟩
  · exact heads₂.of_kept keptResult (by simpa [normalizedHeads] using (show free+8 ≤ finish by omega))
  · exact (keptResult _ (by unfold prime at hmeta; omega)).trans count₂
  · exact normalized₂.keep keptResult ha hb hc (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega)
      (by change normalizedEnd free n (bandSize n) ≤ finish; omega)
  · exact primes₂.of_kept keptResult (by change cover ≤ finish; omega)
  · exact cover₂.of_kept (fun i hi => keptResult i (hi.trans_le hkeyEnd))
  · exact EncodedColorWantedData.of_kept wanted₂ keptResult (by change base ≤ finish; omega)
  · simpa only [hlast,base,EncodedColorPipelineData.controls,cover,p,xs,finish,
      EncodedColorPipelineData.finish] using sources.of_kept keptResult le_rfl
  · dsimp only
    rw [keptResult _ (by change wanted < finish; omega)]
    exact countBound
  · apply lifts.of_kept keptResult
    rw [RawAKeyLists.keys_length]
    change wanted ≤ finish
    omega
  · intro i hi
    exact (keptResult i (by omega)).trans ((keptSources i (by omega)).trans (keptPrime i hi))

end ThreeSum.LightEncodedColorPipeline

end


theorem solution : ∀ {lim : Light.Limits} {d : Nat} {μ : Nat → Int} {src n params row free U : Nat}
  (color :
    ThreeSum.Coloring.Parameter
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (ThreeSum.Scales.inputBits n)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (x : Fin n → Int) (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (hn : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n)
  (hR :
    @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) (ThreeSum.Scales.radix n))
  (hsrc : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) src n) free)
  (hparams :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) params
        (@OfNat.ofNat.{0} Nat (nat_lit 19) (instOfNatNat (nat_lit 19))))
      free)
  (hrow :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) row
        (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
      free)
  (hspace : @LE.le.{0} Nat instLENat (ThreeSum.LightEncodedColorPipeline.space free n U) lim.space)
  (hword :
    @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightEncodedColorPipeline.word n U))
      lim.word)
  (hd :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d (ThreeSum.LightEncodedColorPipeline.depth n))
      lim.depth)
  (hread : Light.Seg μ src (@List.ofFn.{0} Int n x))
  (hbound :
    ∀ (i : Fin n),
      @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup (x i))
        (@Nat.cast.{0} Int instNatCastInt U))
  (hparameters : Light.Seg μ params (ThreeSum.LightParameterInit.values n))
  (hcolor :
    Light.Seg μ row
      (@ThreeSum.ColorParameters.fields
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (ThreeSum.Scales.inputBits n)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        color)),
  Light.Meets lim ThreeSum.LightEncodedColorPipeline.program
    (@OfNat.ofNat.{0} Nat (nat_lit 255) (instOfNatNat (nat_lit 255))) d
    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt src)
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt n)
        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt params)
          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt row)
            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt free) (@List.nil.{0} Int))))))
    μ (ThreeSum.LightEncodedColorPipeline.time n U) fun (r : Int) (ν : Nat → Int) =>
    And (ThreeSum.EncodedColorPipelineData.Output ν free n color x r) (Light.Kept μ ν free) := by
  exact @ThreeSum.LightEncodedColorPipeline.program_meets_sourceProof

#print axioms solution
