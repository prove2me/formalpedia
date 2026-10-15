-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightThreeSumReportingSetupDense.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T09:00:53.935993+00:00
-- url     : https://prove2.me/submissions/901fe1af-9ffb-48a9-a1f5-79007fee8abd

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Aesop
import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_WordSize
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Index
import Definitions.Def_APSPSource_ThreeSumApsp_Util_List
import Definitions.Def_ThreeSum1960614_Analysis
import Definitions.Def_ThreeSum1960614_Machine_Bundle001
import Definitions.Def_ThreeSum1960614_Machine_Bundle002
import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Definitions.Def_ThreeSum1960614_Machine_Bundle004
import Definitions.Def_ThreeSum1960614_Machine_Bundle005
import Definitions.Def_ThreeSum1960614_Machine_Bundle006
import Definitions.Def_ThreeSum1960614_Machine_Bundle007
import Definitions.Def_ThreeSum1960614_Machine_Bundle008
import Definitions.Def_ThreeSum1960614_Machine_Bundle009
import Definitions.Def_ThreeSum1960614_Machine_Bundle010
import Definitions.Def_ThreeSum1960614_Machine_Bundle011
import Definitions.Def_ThreeSum1960614_Machine_Bundle012
import Definitions.Def_ThreeSum1960614_Machine_Bundle013
import Definitions.Def_ThreeSum1960614_Machine_Bundle014
import Definitions.Def_ThreeSum1960614_Machine_Bundle015
import Definitions.Def_ThreeSum1960614_Machine_Bundle016
import Definitions.Def_ThreeSum1960614_Machine_Bundle017
import Definitions.Def_ThreeSum1960614_Machine_Bundle018
import Definitions.Def_ThreeSum1960614_Machine_Bundle019
import Definitions.Def_ThreeSum1960614_Machine_Bundle020
import Definitions.Def_ThreeSum1960614_Machine_Bundle021
import Definitions.Def_ThreeSum1960614_Machine_Bundle022
import Definitions.Def_ThreeSum1960614_Machine_Bundle023
import Definitions.Def_ThreeSum1960614_Machine_Bundle024
import Definitions.Def_ThreeSum1960614_Machine_Bundle025
import Definitions.Def_ThreeSum1960614_Machine_Bundle026
import Definitions.Def_ThreeSum1960614_Machine_Bundle027
import Definitions.Def_ThreeSum1960614_Machine_Bundle028
import Definitions.Def_ThreeSum1960614_Machine_Bundle029
import Definitions.Def_ThreeSum1960614_Machine_Bundle030
import Definitions.Def_ThreeSum1960614_Machine_Bundle031
import Definitions.Def_ThreeSum1960614_Machine_Bundle032
import Definitions.Def_ThreeSum1960614_Machine_Bundle033
import Definitions.Def_ThreeSum1960614_Machine_Bundle034
import Definitions.Def_ThreeSum1960614_Machine_Bundle035
import Definitions.Def_ThreeSum1960614_Machine_Bundle036
import Definitions.Def_ThreeSum1960614_Machine_Bundle037
import Definitions.Def_ThreeSum1960614_Machine_Bundle038
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
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Lean
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
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
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
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_EncodedColorParameterData_reads
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_EncodedColorPipelineData_Stored_of_kept
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_EncodedColorPipelineData_ordered
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightDenseSetup_program_meets
import Theorems.Thm_ThreeSum_BandCandidateRows_fromOwner_sound
import Theorems.Thm_ThreeSum_BandCandidateRows_mem_records_owner
import Theorems.Thm_ThreeSum_BandRawA_mem_aIndices_iff_owner
import Theorems.Thm_ThreeSum_BandRawA_mem_allProducts
import Theorems.Thm_ThreeSum_BandRawA_owner_weightedFalseCount
import Theorems.Thm_ThreeSum_LightPrimePool_prefix_increasing

local instance platformRadixNonzero_a1cd13ab61 (n : ℕ) : NeZero (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) :=
  ⟨Nat.ne_of_gt (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix_pos n)⟩


namespace Filter
end Filter
namespace Finset
end Finset
namespace Light
end Light
namespace Real
end Real
namespace ThreeSum
end ThreeSum
namespace ThreeSum.ArithmeticStageBounds
end ThreeSum.ArithmeticStageBounds
namespace ThreeSum.BandCandidateRows
end ThreeSum.BandCandidateRows
namespace ThreeSum.BandEnumeration
end ThreeSum.BandEnumeration
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition
namespace ThreeSum.BandPrimeChoice
end ThreeSum.BandPrimeChoice
namespace ThreeSum.BandPrimeScales
end ThreeSum.BandPrimeScales
namespace ThreeSum.BandRawA
end ThreeSum.BandRawA
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
namespace ThreeSum.EncodedColorPipelineData
end ThreeSum.EncodedColorPipelineData
namespace ThreeSum.EncodedColorPrimeCosts
end ThreeSum.EncodedColorPrimeCosts
namespace ThreeSum.EncodedColorPrimeData
end ThreeSum.EncodedColorPrimeData
namespace ThreeSum.EncodedColorPrimeReadyData
end ThreeSum.EncodedColorPrimeReadyData
namespace ThreeSum.EncodedColorStageCosts
end ThreeSum.EncodedColorStageCosts
namespace ThreeSum.LightBandPrimeConstruction
end ThreeSum.LightBandPrimeConstruction
namespace ThreeSum.LightBandPrimeStage
end ThreeSum.LightBandPrimeStage
namespace ThreeSum.LightClassFilter
end ThreeSum.LightClassFilter
namespace ThreeSum.LightColorBands
end ThreeSum.LightColorBands
namespace ThreeSum.LightDenseSetup
end ThreeSum.LightDenseSetup
namespace ThreeSum.LightMinimum
end ThreeSum.LightMinimum
namespace ThreeSum.LightPrimeMinimum
end ThreeSum.LightPrimeMinimum
namespace ThreeSum.LightPrimePool
end ThreeSum.LightPrimePool
namespace ThreeSum.LightThreeSumReportingSetupDense
end ThreeSum.LightThreeSumReportingSetupDense
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.SourceFiniteInputs
end ThreeSum.SourceFiniteInputs
namespace ThreeSum.ThreeSumColorBudgets
end ThreeSum.ThreeSumColorBudgets
namespace ThreeSum.ThreeSumReportingSetupData
end ThreeSum.ThreeSumReportingSetupData
namespace ThreeSum.WeightedScore
end ThreeSum.WeightedScore
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds
end ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds
namespace ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
end ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
namespace ThreeSum1960614.Machine.ThreeSum.BandEnumeration
end ThreeSum1960614.Machine.ThreeSum.BandEnumeration
namespace ThreeSum1960614.Machine.ThreeSum.BandPartition
end ThreeSum1960614.Machine.ThreeSum.BandPartition
namespace ThreeSum1960614.Machine.ThreeSum.BandPrimeChoice
end ThreeSum1960614.Machine.ThreeSum.BandPrimeChoice
namespace ThreeSum1960614.Machine.ThreeSum.BandPrimeScales
end ThreeSum1960614.Machine.ThreeSum.BandPrimeScales
namespace ThreeSum1960614.Machine.ThreeSum.BandRawA
end ThreeSum1960614.Machine.ThreeSum.BandRawA
namespace ThreeSum1960614.Machine.ThreeSum.BandScales
end ThreeSum1960614.Machine.ThreeSum.BandScales
namespace ThreeSum1960614.Machine.ThreeSum.BandWeightedScore
end ThreeSum1960614.Machine.ThreeSum.BandWeightedScore
namespace ThreeSum1960614.Machine.ThreeSum.ColorClassLists
end ThreeSum1960614.Machine.ThreeSum.ColorClassLists
namespace ThreeSum1960614.Machine.ThreeSum.CostLedger
end ThreeSum1960614.Machine.ThreeSum.CostLedger
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorLayout
end ThreeSum1960614.Machine.ThreeSum.EncodedColorLayout
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData
end ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData
end ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeCosts
end ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeCosts
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeData
end ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeData
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeReadyData
end ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeReadyData
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorStageCosts
end ThreeSum1960614.Machine.ThreeSum.EncodedColorStageCosts
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.LightBandPrimeConstruction
end ThreeSum1960614.Machine.ThreeSum.LightBandPrimeConstruction
namespace ThreeSum1960614.Machine.ThreeSum.LightBandPrimeStage
end ThreeSum1960614.Machine.ThreeSum.LightBandPrimeStage
namespace ThreeSum1960614.Machine.ThreeSum.LightClassFilter
end ThreeSum1960614.Machine.ThreeSum.LightClassFilter
namespace ThreeSum1960614.Machine.ThreeSum.LightColorBands
end ThreeSum1960614.Machine.ThreeSum.LightColorBands
namespace ThreeSum1960614.Machine.ThreeSum.LightDenseSetup
end ThreeSum1960614.Machine.ThreeSum.LightDenseSetup
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule
namespace ThreeSum1960614.Machine.ThreeSum.LightMinimum
end ThreeSum1960614.Machine.ThreeSum.LightMinimum
namespace ThreeSum1960614.Machine.ThreeSum.LightPrimeMinimum
end ThreeSum1960614.Machine.ThreeSum.LightPrimeMinimum
namespace ThreeSum1960614.Machine.ThreeSum.LightPrimePool
end ThreeSum1960614.Machine.ThreeSum.LightPrimePool
namespace ThreeSum1960614.Machine.ThreeSum.LightThreeSumReportingSetupDense
end ThreeSum1960614.Machine.ThreeSum.LightThreeSumReportingSetupDense
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.Scales
end ThreeSum1960614.Machine.ThreeSum.Scales
namespace ThreeSum1960614.Machine.ThreeSum.SourceFiniteInputs
end ThreeSum1960614.Machine.ThreeSum.SourceFiniteInputs
namespace ThreeSum1960614.Machine.ThreeSum.ThreeSumColorBudgets
end ThreeSum1960614.Machine.ThreeSum.ThreeSumColorBudgets
namespace ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData
end ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData
namespace ThreeSum1960614.Machine.ThreeSum.WeightedScore
end ThreeSum1960614.Machine.ThreeSum.WeightedScore
namespace ThreeSum1960614.Machine.ThreeSumApsp
end ThreeSum1960614.Machine.ThreeSumApsp
namespace ThreeSumApsp
end ThreeSumApsp

namespace ThreeSum1960614.Machine

/-!
# Consecutive bands of a strictly increasing array

The last band is truncated. Every input position belongs to its quotient
band, the bands are strictly separated, and each band has at most `g` entries.
The quotient in these specifications is realized by `LightBandPartition`.
-/

namespace ThreeSum.BandPartition
open _root_.ThreeSum.BandPartition






theorem size_le (n g : ℕ) : _root_.ThreeSum.BandPartition.size n g ≤ n := by
  unfold _root_.ThreeSum.BandPartition.size
  split_ifs with h
  · omega
  · have hdiv := Nat.div_le_self (n-1) g
    omega

theorem size_mono {n m g : ℕ} (h : n ≤ m) : _root_.ThreeSum.BandPartition.size n g ≤ _root_.ThreeSum.BandPartition.size m g := by
  by_cases hn : n = 0
  · simp [_root_.ThreeSum.BandPartition.size,hn]
  · have hm : m ≠ 0 := by omega
    have hd := Nat.div_le_div_right (c := g) (show n-1 ≤ m-1 by omega)
    simp only [_root_.ThreeSum.BandPartition.size,if_neg hn,if_neg hm]
    omega























end ThreeSum.BandPartition

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The actual integer block schedule

All four size parameters below are executable natural-number functions.
The finite bounds and limits concern these functions, including the even
rounding of the cube root and the divisibility constraints on the number
of blocks.  No asymptotic size premise is imposed on the schedule.
-/

namespace ThreeSum.Scales
open _root_.ThreeSum.Scales


open _root_.Filter
open _root_.Real
open scoped _root_.Topology





















































noncomputable section

































































theorem primeDepth_upper (R : ℕ → ℕ) {n : ℕ} (hR : 4 ≤ R n) :
    4 * (4 * _root_.ThreeSum.Scales.primeWindow n) ^ _root_.ThreeSum.Scales.primeDepth R n ≤ R n := by
  have hr : R n / 4 ≠ 0 := by omega
  have h := Nat.pow_log_le_self (4 * _root_.ThreeSum.Scales.primeWindow n) hr
  have h4 := Nat.mul_le_mul_left 4 h
  have hd := Nat.div_mul_le_self (R n) 4
  simpa [_root_.ThreeSum.Scales.primeDepth, Nat.mul_comm] using h4.trans (by simpa [Nat.mul_comm] using hd)





































































end

end ThreeSum.Scales

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

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
open _root_.Light


variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

/-! ## Runs -/

/-- A procedure of a program is a procedure, with the same number, of the program with more
procedures appended. -/
theorem getElem?_append_of_eq_some {P : _root_.ThreeSum1960614.Machine.Light.Program} {p : ℕ} {body : _root_.ThreeSum1960614.Machine.Light.Stmt} (h : P[p]? = some body)
    (R : _root_.ThreeSum1960614.Machine.Light.Program) : (P ++ R)[p]? = some body := by
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 h).1]
  exact h





/-- A run stays a run when procedures are appended to the program. -/
theorem Exec.append {s : _root_.ThreeSum1960614.Machine.Light.Stmt} {σ σ' : _root_.ThreeSum1960614.Machine.Light.State} {c : ℕ} (h : _root_.ThreeSum1960614.Machine.Light.Exec lim P d s σ σ' c) (R : _root_.ThreeSum1960614.Machine.Light.Program) :
    _root_.ThreeSum1960614.Machine.Light.Exec lim (P ++ R) d s σ σ' c := by
  induction h with
  | skip => exact _root_.ThreeSum1960614.Machine.Light.Exec.skip
  | set h => exact _root_.ThreeSum1960614.Machine.Light.Exec.set h
  | store h₁ h₂ h₃ => exact _root_.ThreeSum1960614.Machine.Light.Exec.store h₁ h₂ h₃
  | seq _ _ ih₁ ih₂ => exact _root_.ThreeSum1960614.Machine.Light.Exec.seq ih₁ ih₂
  | iteTrue h₁ h₂ _ ih => exact _root_.ThreeSum1960614.Machine.Light.Exec.iteTrue h₁ h₂ ih
  | iteFalse h₁ h₂ _ ih => exact _root_.ThreeSum1960614.Machine.Light.Exec.iteFalse h₁ h₂ ih
  | whileFalse h₁ h₂ => exact _root_.ThreeSum1960614.Machine.Light.Exec.whileFalse h₁ h₂
  | whileTrue h₁ h₂ _ _ ih₁ ih₂ => exact _root_.ThreeSum1960614.Machine.Light.Exec.whileTrue h₁ h₂ ih₁ ih₂
  | call h₁ h₂ h₃ _ ih => exact _root_.ThreeSum1960614.Machine.Light.Exec.call h₁ (_root_.ThreeSum1960614.Machine.Light.getElem?_append_of_eq_some h₂ R) h₃ ih

/-! ## The rules -/





/-- What is proved about a program holds for the program with more procedures appended. -/
theorem Ends.append {s σ T Q} (h : _root_.ThreeSum1960614.Machine.Light.Ends lim P d s σ T Q) (R : _root_.ThreeSum1960614.Machine.Light.Program) :
    _root_.ThreeSum1960614.Machine.Light.Ends lim (P ++ R) d s σ T Q := by
  obtain ⟨σ', c, he, hc, hq⟩ := h
  exact ⟨σ', c, he.append R, hc, hq⟩























/-! ## Notation for writing programs

Not trusted: a theorem about a program does not depend on how the program was typed in. -/


















/-! ## Simplification -/

attribute [simp] _root_.ThreeSum1960614.Machine.Light.Expr.val _root_.ThreeSum1960614.Machine.Light.Expr.cost _root_.ThreeSum1960614.Machine.Light.Expr.Safe _root_.Light.Op.eval _root_.ThreeSum1960614.Machine.Light.Cond.Holds _root_.ThreeSum1960614.Machine.Light.Cond.cost _root_.ThreeSum1960614.Machine.Light.Cond.Safe _root_.Light.frame







/-! ## The limits -/









end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

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
open _root_.Light


variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

/-! ## Specifications of procedures -/



section
variable {p : ℕ} {vals : List ℤ} {μ : ℕ → ℤ} {T T' : ℕ} {R R' : ℤ → (ℕ → ℤ) → Prop}

/-- From a theorem about a body to the specification. -/
theorem Meets.of_body {args : List ℤ} {Q : ℤ → (ℕ → ℤ) → Prop} {body : _root_.ThreeSum1960614.Machine.Light.Stmt}
    (hp : P[p]? = some body)
    (h : _root_.ThreeSum1960614.Machine.Light.Ends lim P d body ⟨_root_.Light.frame args, μ⟩ T fun σ' => Q (σ'.loc 0) σ'.mem) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P p d args μ T Q :=
  ⟨body, hp, h⟩







/-- A specification holds for the program with more procedures appended. -/
theorem Meets.append (h : _root_.ThreeSum1960614.Machine.Light.Meets lim P p d vals μ T R) (P' : _root_.ThreeSum1960614.Machine.Light.Program) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim (P ++ P') p d vals μ T R := by
  obtain ⟨body, hp, he⟩ := h
  exact ⟨body, _root_.ThreeSum1960614.Machine.Light.getElem?_append_of_eq_some hp P', he.append P'⟩

end

/-! ## The rule for calls -/

section
variable {loc μ : ℕ → ℤ} {l : List ℤ} {T T' p x : ℕ} {args : List _root_.ThreeSum1960614.Machine.Light.Expr} {vals : List ℤ}
  {R : ℤ → (ℕ → ℤ) → Prop} {Q : _root_.ThreeSum1960614.Machine.Light.State → Prop} {s : _root_.ThreeSum1960614.Machine.Light.Stmt}









end

end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

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
open _root_.Light


open _root_.ThreeSumApsp
open _root_.ThreeSum1960614.Machine.ThreeSumApsp





variable {μ μ' μ'' : ℕ → ℤ} {a b n : ℕ} {l l₁ l₂ : List ℤ} {x : ℤ}













/-- Reading a cell of a segment, with a default value for the list. -/
theorem Seg.getD (h : _root_.ThreeSum1960614.Machine.Light.Seg μ a l) {i : ℕ} (hi : i < l.length) (d : ℤ) : μ (a + i) = l.getD i d := by
  rw [h i hi, List.getD_eq_getElem _ _ hi]





































/-- Reading a cell of a segment of natural numbers. -/
theorem SegN.read {l : List ℕ} (h : _root_.ThreeSum1960614.Machine.Light.SegN μ a l) {i : ℕ} (hi : i < l.length) :
    μ (a + i) = ((l.getD i 0 : ℕ) : ℤ) := by
  rw [h i (by simpa using hi), List.getElem_map, List.getD_eq_getElem _ _ hi]



























end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The exact physical band-owner record order

There is one four-cell record for every owner-table cell, in BC, AB, AC
rectangle order. A zero flag is a lookup miss. Successful records retain
their physical owner slot even when several owners produce the same triple.
-/

namespace ThreeSum.BandCandidateRows
open _root_.ThreeSum.BandCandidateRows


open _root_.ThreeSum.BandEnumeration
open _root_.ThreeSum1960614.Machine.ThreeSum.BandEnumeration

set_option maxHeartbeats 1400000
set_option maxRecDepth 7000



























theorem rect_length (m n : ℕ) (F : ℕ → ℕ → _root_.ThreeSum.BandCandidateRows.Record) : (_root_.ThreeSum.BandCandidateRows.rect m n F).length=m*n := by
  simp [_root_.ThreeSum.BandCandidateRows.rect,List.length_flatMap]

theorem records_length (A B C : _root_.ThreeSum.BandEnumeration.Family) :
    (_root_.ThreeSum.BandCandidateRows.records A B C).length=_root_.ThreeSum.LightBandEnumeration.count A.size B.size C.size := by
  simp only [_root_.ThreeSum.BandCandidateRows.records,List.length_append,_root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows.rect_length,_root_.ThreeSum.LightBandEnumeration.count]
  omega











theorem make_flag (mode : _root_.ThreeSum.BandCandidateRows.Mode) (i j r : ℕ) :
    (_root_.ThreeSum.BandCandidateRows.make mode i j r).flag=0 ∨ (_root_.ThreeSum.BandCandidateRows.make mode i j r).flag=1 := by
  cases mode <;> simp only [_root_.ThreeSum.BandCandidateRows.make] <;> split_ifs <;> simp













end ThreeSum.BandCandidateRows

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Stable extraction of one color class from the original signed array

The program reads stored colors and original values. It writes a length
header followed by exactly the selected values, optionally negated. Repeated
values are preserved; deduplication belongs to the later normalization pass.
-/

namespace ThreeSum.LightClassFilter
open _root_.ThreeSum.LightClassFilter


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

set_option maxHeartbeats 1200000







theorem items_length_le (x : ℕ → ℤ) (color : ℕ → ℕ) (want : ℕ) (scale : ℤ) (n : ℕ) :
    (_root_.ThreeSum.LightClassFilter.items x color want scale n).length ≤ n := by
  simpa only [_root_.ThreeSum.LightClassFilter.items,List.length_map,List.length_range] using
    List.length_filter_le (p := fun i => decide (color i = want)) (l := List.range n)

theorem mem_items (x : ℕ → ℤ) (color : ℕ → ℕ) (want : ℕ) (scale : ℤ) (n : ℕ) (z : ℤ) :
    z ∈ _root_.ThreeSum.LightClassFilter.items x color want scale n ↔ ∃ i, i < n ∧ color i = want ∧ scale*x i = z := by
  simp [_root_.ThreeSum.LightClassFilter.items,and_assoc]









variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}







end ThreeSum.LightClassFilter

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# A finite array minimum scan in the benchmark language

The selected index is a deterministic left-to-right minimum. Its value
can therefore instantiate the exact mean bound for offset balancing.
-/

namespace ThreeSum.LightMinimum
open _root_.ThreeSum.LightMinimum


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light



theorem least_lt (f : ℕ → ℤ) {n : ℕ} (hn : 0 < n) : _root_.ThreeSum.LightMinimum.least f n < n := by
  induction n with
  | zero => omega
  | succ n ih =>
      cases n with
      | zero => simp [_root_.ThreeSum.LightMinimum.least]
      | succ n =>
          have h := ih (by omega)
          unfold _root_.ThreeSum.LightMinimum.least
          split <;> omega











variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}



end ThreeSum.LightMinimum

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Executing the candidate prime pool

This fixed program scans the integers in `(y,4*y]`, invokes the concrete
trial-division procedure, and writes every prime exactly once in increasing
order. The returned length and written array are the exact candidate pool
used by the contraction and auxiliary-weight theorems.
-/

namespace ThreeSum.LightPrimePool
open _root_.ThreeSum.LightPrimePool


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000



theorem prefix_length_le (y i : ℕ) : (_root_.ThreeSum.LightPrimePool.scanned y i).length ≤ i := by
  induction i with
  | zero => simp [_root_.ThreeSum.LightPrimePool.scanned]
  | succ i ih =>
      unfold _root_.ThreeSum.LightPrimePool.scanned
      split
      · simp only [List.length_append,List.length_singleton]
        omega
      · omega





theorem prefix_nodup (y i : ℕ) : (_root_.ThreeSum.LightPrimePool.scanned y i).Nodup :=
  (_root_.ThreeSum.LightPrimePool.prefix_increasing y i).imp (fun h => Nat.ne_of_lt h)






theorem values_nodup (y : ℕ) : (_root_.ThreeSum.LightPrimePool.values y).Nodup := _root_.ThreeSum1960614.Machine.ThreeSum.LightPrimePool.prefix_nodup y (3*y)
theorem size_le (y : ℕ) : _root_.ThreeSum.LightPrimePool.size y ≤ 3*y := _root_.ThreeSum1960614.Machine.ThreeSum.LightPrimePool.prefix_length_le y (3*y)









theorem prime_spec {y i : ℕ} (hi : i < _root_.ThreeSum.LightPrimePool.size y) :
    Nat.Prime (_root_.ThreeSum.LightPrimePool.prime y i) ∧ y < _root_.ThreeSum.LightPrimePool.prime y i ∧ _root_.ThreeSum.LightPrimePool.prime y i ≤ 4*y :=
  _root_.ThreeSum.LightPrimePool.mem_values.mp (_root_.ThreeSum.LightPrimePool.prime_mem hi)

theorem prime_injective {y i j : ℕ} (hi : i < _root_.ThreeSum.LightPrimePool.size y) (hj : j < _root_.ThreeSum.LightPrimePool.size y)
    (heq : _root_.ThreeSum.LightPrimePool.prime y i = _root_.ThreeSum.LightPrimePool.prime y j) : i = j :=
  (List.getD_inj hi hj (_root_.ThreeSum1960614.Machine.ThreeSum.LightPrimePool.values_nodup y)).mp heq



theorem values_nonempty {y : ℕ} (hy : 0 < y) : _root_.ThreeSum.LightPrimePool.values y ≠ [] := by
  obtain ⟨p,hp,hlo,hhi⟩ := Nat.exists_prime_lt_and_le_two_mul y hy.ne'
  have hmem : p ∈ _root_.ThreeSum.LightPrimePool.values y := _root_.ThreeSum.LightPrimePool.mem_values.mpr ⟨hp,hlo,by omega⟩
  intro heq
  simpa only [heq,List.not_mem_nil] using hmem

theorem size_pos {y : ℕ} (hy : 0 < y) : 0 < _root_.ThreeSum.LightPrimePool.size y :=
  List.length_pos_iff.mpr (_root_.ThreeSum1960614.Machine.ThreeSum.LightPrimePool.values_nonempty hy)



















variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}









end ThreeSum.LightPrimePool

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # List and memory interfaces for the exact candidate record array -/

namespace ThreeSum.BandCandidateRows
open _root_.ThreeSum.BandCandidateRows


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandEnumeration
open _root_.ThreeSum1960614.Machine.ThreeSum.BandEnumeration

set_option maxHeartbeats 1300000



theorem records_sound {A B C : _root_.ThreeSum.BandEnumeration.Family} {r : _root_.ThreeSum.BandCandidateRows.Record}
    (hr : r ∈ _root_.ThreeSum.BandCandidateRows.records A B C) (hf : r.flag=1) :
    r.a < A.size ∧ r.b < B.size ∧ r.c < C.size ∧
      _root_.ThreeSum.Bands.Relevant A.lower A.upper B.lower B.upper C.lower C.upper (r.a,r.b,r.c) := by
  obtain ⟨o,rfl⟩ := _root_.ThreeSum.BandCandidateRows.mem_records_owner hr
  exact _root_.ThreeSum.BandCandidateRows.fromOwner_sound A B C o hf

theorem records_flag {A B C : _root_.ThreeSum.BandEnumeration.Family} {r : _root_.ThreeSum.BandCandidateRows.Record} (hr : r ∈ _root_.ThreeSum.BandCandidateRows.records A B C) :
    r.flag=0 ∨ r.flag=1 := by
  obtain ⟨o,rfl⟩ := _root_.ThreeSum.BandCandidateRows.mem_records_owner hr
  rcases o with ⟨j,k⟩ | ⟨i,j | k⟩ <;> exact _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows.make_flag _ _ _ _











end ThreeSum.BandCandidateRows

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact original-position semantics of the constructed color-class lists

The machine keeps repeated values within a class and negates the third
class. The list membership witnesses are original positions. Any binary
width large enough for the indices suffices for the deterministic family.
-/

namespace ThreeSum.ColorClassLists
open _root_.ThreeSum.ColorClassLists


open _root_.ThreeSum.LightClassFilter
open _root_.ThreeSum1960614.Machine.ThreeSum.LightClassFilter













theorem length_classList_le {n W : ℕ} (p : _root_.ThreeSum.Coloring.Parameter W) (x : Fin n → ℤ)
    (c : ℕ) (scale : ℤ) : (_root_.ThreeSum.ColorClassLists.classList p x c scale).length ≤ n :=
  _root_.ThreeSum1960614.Machine.ThreeSum.LightClassFilter.items_length_le ..













end ThreeSum.ColorClassLists

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Executing deterministic prime-score minimization

The same finite prime array supplies the candidate multipliers and the
auxiliary tests. The program streams exact scores at `q * primes i`, retaining
the first minimum. All weighted-score calls reuse one scratch region.
-/

namespace ThreeSum.LightPrimeMinimum
open _root_.ThreeSum.LightPrimeMinimum


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.WeightedScore
open _root_.ThreeSum1960614.Machine.ThreeSum.WeightedScore

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000











theorem score_congr {primes : ℕ → ℕ} {s q nA nB nC : ℕ} {A A' B B' C C' : ℕ → ℤ}
    (ha : ∀ i < nA, A i = A' i) (hb : ∀ i < nB, B i = B' i)
    (hc : ∀ i < nC, C i = C' i) :
    _root_.ThreeSum.WeightedScore.score primes s q nA nB nC A B C = _root_.ThreeSum.WeightedScore.score primes s q nA nB nC A' B' C' := by
  unfold _root_.ThreeSum.WeightedScore.score _root_.ThreeSum.Arithmetic.weightedFalseCount
  apply Finset.sum_congr rfl
  intro t ht
  simp only [_root_.ThreeSum.ModuloCounts.triples, Finset.mem_product, Finset.mem_range] at ht
  simp only [_root_.ThreeSum.ModuloCounts.difference, ha _ ht.1, hb _ ht.2.1, hc _ ht.2.2]
  rfl











variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}













end ThreeSum.LightPrimeMinimum

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The aggregate weighted score of physical band-owner candidates

Each flagged owner contributes the score of its three actual truncated
bands. Owner multiplicities are retained. The contraction and initial bound
therefore apply to the same quadratic catalog that the program scans.
-/

namespace ThreeSum.BandWeightedScore
open _root_.ThreeSum.BandWeightedScore


open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
open _root_.Finset
open scoped _root_.BigOperators

set_option maxHeartbeats 1600000
set_option maxRecDepth 8000







theorem position_lt {n g a i : ℕ} (hi : i < _root_.ThreeSum.BandWeightedScore.length n g a) : a*g+i < n := by
  have hh := min_le_right g (n-a*g)
  unfold _root_.ThreeSum.BandWeightedScore.length at hi
  omega



















theorem block_congr {primes : ℕ → ℕ} {s q nA nB nC g : ℕ}
    {A A' B B' C C' : ℕ → ℤ} (r : _root_.ThreeSum.BandCandidateRows.Record)
    (hA : ∀ i < nA, A i=A' i) (hB : ∀ i < nB, B i=B' i) (hC : ∀ i < nC, C i=C' i) :
    _root_.ThreeSum.BandWeightedScore.block primes s q nA nB nC g A B C r=_root_.ThreeSum.BandWeightedScore.block primes s q nA nB nC g A' B' C' r := by
  unfold _root_.ThreeSum.BandWeightedScore.block
  split_ifs
  · exact _root_.ThreeSum1960614.Machine.ThreeSum.LightPrimeMinimum.score_congr
      (fun i hi => hA _ (_root_.ThreeSum1960614.Machine.ThreeSum.BandWeightedScore.position_lt hi)) (fun i hi => hB _ (_root_.ThreeSum1960614.Machine.ThreeSum.BandWeightedScore.position_lt hi))
      (fun i hi => hC _ (_root_.ThreeSum1960614.Machine.ThreeSum.BandWeightedScore.position_lt hi))
  · rfl

theorem score_congr {primes : ℕ → ℕ} {s q nA nB nC g : ℕ}
    {A A' B B' C C' : ℕ → ℤ} (rs : List _root_.ThreeSum.BandCandidateRows.Record)
    (hA : ∀ i < nA, A i=A' i) (hB : ∀ i < nB, B i=B' i) (hC : ∀ i < nC, C i=C' i) :
    _root_.ThreeSum.BandWeightedScore.score primes s q nA nB nC g A B C rs=_root_.ThreeSum.BandWeightedScore.score primes s q nA nB nC g A' B' C' rs := by
  unfold _root_.ThreeSum.BandWeightedScore.score _root_.ThreeSum.BandWeightedScore.partialScore
  exact sum_congr rfl fun i _ => _root_.ThreeSum1960614.Machine.ThreeSum.BandWeightedScore.block_congr (rs.getD i default) hA hB hC





end ThreeSum.BandWeightedScore

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Original input to normalized color bands

This fixed program computes index colors, writes the three class arrays and
their headers, then reads those headers into the existing normalization and
owner-table program. All buffers and resource bounds depend on the original
input length, rather than on externally supplied color-class lengths.
-/

namespace ThreeSum.LightColorBands
open _root_.ThreeSum.LightColorBands


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.ColorClassLists
open _root_.ThreeSum1960614.Machine.ThreeSum.ColorClassLists

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000








theorem class_bounded {n W U : ℕ} (p : _root_.ThreeSum.Coloring.Parameter W) (x : Fin n → ℤ)
    (c : ℕ) (scale : ℤ) (hs : |scale| ≤ 1) (hx : ∀ i, |x i| ≤ (U : ℤ)) :
    ∀ z ∈ _root_.ThreeSum.ColorClassLists.classList p x c scale, |z| ≤ (U : ℤ) := by
  intro z hz
  obtain ⟨i,hi,_,rfl⟩ :=
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightClassFilter.mem_items (_root_.ThreeSum.ColorClassLists.value x) (_root_.ThreeSum.LightColorIndex.color p) c scale n z).mp hz
  have hv : |_root_.ThreeSum.ColorClassLists.value x i| ≤ (U : ℤ) := by
    simpa only [_root_.ThreeSum.ColorClassLists.value,hi,dite_true] using hx ⟨i,hi⟩
  rw [abs_mul]
  calc
    |scale| * |_root_.ThreeSum.ColorClassLists.value x i| ≤ 1 * (U : ℤ) :=
      mul_le_mul hs hv (abs_nonneg _) (by norm_num)
    _ = (U : ℤ) := one_mul _



variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}













end ThreeSum.LightColorBands

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# A common contracting modulus for the complete band-owner catalog

The same deterministic first-minimum rule is applied to the sum of every
flagged owner's score. These are joint choices for all bands, rather than
independent moduli whose contractions could not be combined.
-/

namespace ThreeSum.BandPrimeChoice
open _root_.ThreeSum.BandPrimeChoice


open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
open _root_.ThreeSum.BandWeightedScore
open _root_.ThreeSum1960614.Machine.ThreeSum.BandWeightedScore
open _root_.Finset
open scoped _root_.BigOperators

set_option maxHeartbeats 1400000
set_option maxRecDepth 8000







theorem chosenIndex_lt (primes : ℕ → ℕ) {s q nA nB nC g : ℕ}
    (A B C : ℕ → ℤ) (rs : List _root_.ThreeSum.BandCandidateRows.Record) (hs : 0 < s) :
    _root_.ThreeSum.BandPrimeChoice.chosenIndex primes s q nA nB nC g A B C rs < s := _root_.ThreeSum1960614.Machine.ThreeSum.LightMinimum.least_lt _ hs







theorem modulus_bounds (primes : ℕ → ℕ) {s nA nB nC g : ℕ}
    (A B C : ℕ → ℤ) (rs : List _root_.ThreeSum.BandCandidateRows.Record) (hs : 0 < s) (y Y r : ℕ)
    (hlo : ∀ i < s, y ≤ primes i) (hhi : ∀ i < s, primes i ≤ Y) :
    y^r ≤ _root_.ThreeSum.BandPrimeChoice.modulus primes s nA nB nC g A B C rs r ∧
      _root_.ThreeSum.BandPrimeChoice.modulus primes s nA nB nC g A B C rs r ≤ Y^r := by
  induction r with
  | zero => simp [_root_.ThreeSum.BandPrimeChoice.modulus]
  | succ r ih =>
    have hidx := _root_.ThreeSum1960614.Machine.ThreeSum.BandPrimeChoice.chosenIndex_lt (q := _root_.ThreeSum.BandPrimeChoice.modulus primes s nA nB nC g A B C rs r)
      (nA := nA) (nB := nB) (nC := nC) (g := g) primes A B C rs hs
    constructor
    · simpa only [_root_.ThreeSum.BandPrimeChoice.modulus,pow_succ,_root_.ThreeSum.BandPrimeChoice.chosenPrime] using Nat.mul_le_mul ih.1 (hlo _ hidx)
    · simpa only [_root_.ThreeSum.BandPrimeChoice.modulus,pow_succ,_root_.ThreeSum.BandPrimeChoice.chosenPrime] using Nat.mul_le_mul ih.2 (hhi _ hidx)

theorem modulus_pos (primes : ℕ → ℕ) {s nA nB nC g : ℕ}
    (A B C : ℕ → ℤ) (rs : List _root_.ThreeSum.BandCandidateRows.Record) (hs : 0 < s)
    (hprime : ∀ i < s, Nat.Prime (primes i)) (r : ℕ) :
    0 < _root_.ThreeSum.BandPrimeChoice.modulus primes s nA nB nC g A B C rs r := by
  have hh := (_root_.ThreeSum1960614.Machine.ThreeSum.BandPrimeChoice.modulus_bounds (nA := nA) (nB := nB) (nC := nC) (g := g) primes A B C rs hs 1
    (Finset.sup (range s) primes) r
    (fun i hi => (hprime i hi).pos)
    (fun i hi => Finset.le_sup (mem_range.mpr hi))).1
  rw [one_pow] at hh
  omega









end ThreeSum.BandPrimeChoice

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Each physical A incidence retains exactly its owner's B/C product

The products in this file are mathematical counting domains. The actual
catalog is still constructed by the verified quadratic owner loop and
linear band copies. Distinct owner products are disjoint because their
physical A incidence indices differ, even when their values coincide.
-/

namespace ThreeSum.BandRawA
open _root_.ThreeSum.BandRawA


open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
open _root_.Finset
open scoped _root_.BigOperators

set_option maxHeartbeats 1900000
set_option maxRecDepth 8000



















theorem mem_ownerProduct {nA nB nC g s : ℕ} {rs : List _root_.ThreeSum.BandCandidateRows.Record} {t : ℕ × ℕ × ℕ}
    (hs : s < rs.length) :
    t ∈ _root_.ThreeSum.BandRawA.ownerProduct nA nB nC g rs s ↔
      t.1 < (_root_.ThreeSum.BandRawA.items nA g rs).length ∧ (_root_.ThreeSum.BandRawA.labelAt nA g rs t.1).owner=s ∧
        t.2.1 ∈ _root_.ThreeSum.BandRawA.bandPositions nB g (rs.getD s default).b ∧
        t.2.2 ∈ _root_.ThreeSum.BandRawA.bandPositions nC g (rs.getD s default).c := by
  simp only [_root_.ThreeSum.BandRawA.ownerProduct,mem_product,_root_.ThreeSum.BandRawA.mem_aIndices_iff_owner hs,and_assoc]

theorem ownerProduct_disjoint {nA nB nC g s t : ℕ} {rs : List _root_.ThreeSum.BandCandidateRows.Record}
    (hs : s < rs.length) (ht : t < rs.length) (hst : s ≠ t) :
    Disjoint (_root_.ThreeSum.BandRawA.ownerProduct nA nB nC g rs s) (_root_.ThreeSum.BandRawA.ownerProduct nA nB nC g rs t) := by
  apply disjoint_left.mpr
  intro x hx hy
  have hs' := (_root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.mem_ownerProduct hs).mp hx
  have ht' := (_root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.mem_ownerProduct ht).mp hy
  exact hst (hs'.2.1.symm.trans ht'.2.1)









theorem sum_allProducts (F : (ℕ × ℕ × ℕ) → ℕ) (nA nB nC g : ℕ)
    (rs : List _root_.ThreeSum.BandCandidateRows.Record) :
    (∑ t ∈ _root_.ThreeSum.BandRawA.allProducts nA nB nC g rs, F t)=
      ∑ s ∈ range rs.length, ∑ t ∈ _root_.ThreeSum.BandRawA.ownerProduct nA nB nC g rs s, F t := by
  unfold _root_.ThreeSum.BandRawA.allProducts
  apply sum_biUnion
  intro s hs t ht hst
  exact _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.ownerProduct_disjoint (mem_range.mp hs) (mem_range.mp ht) hst



end ThreeSum.BandRawA

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The aggregate prime score is the exact physical incidence-product score

The executable A catalog supplies the first-coordinate values. Its owner
metadata supplies the B/C slices. Thus the mathematical score summed by
the actual prime selector counts this same domain with all multiplicities.
-/

namespace ThreeSum.BandRawA
open _root_.ThreeSum.BandRawA


open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
open _root_.Finset
open scoped _root_.BigOperators

set_option maxHeartbeats 1900000
set_option maxRecDepth 8000







theorem all_weightedFalseCount (primes : ℕ → ℕ) (aux q nA nB nC g : ℕ)
    (A B C : ℕ → ℤ) (rs : List _root_.ThreeSum.BandCandidateRows.Record) :
    _root_.ThreeSum.Arithmetic.weightedFalseCount (_root_.ThreeSum.BandRawA.allProducts nA nB nC g rs)
      (_root_.ThreeSum.ModuloCounts.difference (_root_.ThreeSum.BandRawA.valueAt nA g rs A) B C)
      (_root_.ThreeSum.Auxiliary.moduli (_root_.ThreeSum.WeightedScore.auxiliarySet primes aux)) q=
      _root_.ThreeSum.BandWeightedScore.score primes aux q nA nB nC g A B C rs := by
  unfold _root_.ThreeSum.Arithmetic.weightedFalseCount
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.sum_allProducts]
  unfold _root_.ThreeSum.BandWeightedScore.score _root_.ThreeSum.BandWeightedScore.partialScore
  apply sum_congr rfl
  intro s hs
  exact _root_.ThreeSum.BandRawA.owner_weightedFalseCount primes aux q nA nB nC g A B C rs (mem_range.mp hs)













end ThreeSum.BandRawA

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Construct the prime pool and common contracting modulus from band records

The fixed host constructs the candidate prime array, then executes the
aggregate modulus chain on every owner record. The physical prime array and
every prefix modulus remain available to the encoder and reporting stages.
-/

namespace ThreeSum.LightBandPrimeConstruction
open _root_.ThreeSum.LightBandPrimeConstruction


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows

set_option maxHeartbeats 2200000
set_option maxRecDepth 10000



theorem modulus_bounds {y nA nB nC g : ℕ}
    (A B C : ℕ → ℤ) (rs : List _root_.ThreeSum.BandCandidateRows.Record) (levels : ℕ) (hy : 0 < y) :
    y^levels ≤ _root_.ThreeSum.LightBandPrimeConstruction.modulus y nA nB nC g A B C rs levels ∧
      _root_.ThreeSum.LightBandPrimeConstruction.modulus y nA nB nC g A B C rs levels ≤ (4*y)^levels :=
  _root_.ThreeSum1960614.Machine.ThreeSum.BandPrimeChoice.modulus_bounds (_root_.ThreeSum.LightPrimePool.prime y) A B C rs
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightPrimePool.size_pos hy) y (4*y) levels
    (fun i hi => (_root_.ThreeSum1960614.Machine.ThreeSum.LightPrimePool.prime_spec hi).2.1.le)
    (fun i hi => (_root_.ThreeSum1960614.Machine.ThreeSum.LightPrimePool.prime_spec hi).2.2)















variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {d : ℕ} {μ : ℕ → ℤ}
    {a b c nA nB nC g recs y levels free maxMod U : ℕ}



end ThreeSum.LightBandPrimeConstruction

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Finite scale guarantees for the executed physical-owner modulus

These theorems instantiate the previously proved size-only mass bounds with
the common modulus actually constructed from the candidate record array.
The weighted count is over physical A incidences and their own B/C bands.
-/

namespace ThreeSum.BandPrimeScales
open _root_.ThreeSum.BandPrimeScales


open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger

set_option maxHeartbeats 1600000
set_option maxRecDepth 9000









theorem modulus_bounds (n nA nB nC : ℕ) (A B C : ℕ → ℤ) (rs : List _root_.ThreeSum.BandCandidateRows.Record) :
    _root_.ThreeSum.Scales.primeWindow n^_root_.ThreeSum.Scales.primeDepth _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n ≤ _root_.ThreeSum1960614.Machine.ThreeSum.BandPrimeScales.modulus n nA nB nC A B C rs ∧
      _root_.ThreeSum1960614.Machine.ThreeSum.BandPrimeScales.modulus n nA nB nC A B C rs ≤ (4*_root_.ThreeSum.Scales.primeWindow n)^_root_.ThreeSum.Scales.primeDepth _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n :=
  _root_.ThreeSum1960614.Machine.ThreeSum.LightBandPrimeConstruction.modulus_bounds A B C rs _ (by have := _root_.ThreeSum.Scales.primeWindow_ge_two n; omega)

/-- The integer guard used by the three-lift residue construction. -/
theorem modulus_guard {n nA nB nC : ℕ} (A B C : ℕ → ℤ) (rs : List _root_.ThreeSum.BandCandidateRows.Record)
    (hR : 4 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) : 4*_root_.ThreeSum1960614.Machine.ThreeSum.BandPrimeScales.modulus n nA nB nC A B C rs ≤ _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n :=
  (Nat.mul_le_mul_left 4 (_root_.ThreeSum1960614.Machine.ThreeSum.BandPrimeScales.modulus_bounds n nA nB nC A B C rs).2).trans
    (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.primeDepth_upper _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix hR)



/-- Every candidate and auxiliary product fits the existing arithmetic cap. -/
theorem resource_modulus_bound {n : ℕ} (hR : 4 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) :
    (4*_root_.ThreeSum.Scales.primeWindow n)^(_root_.ThreeSum.Scales.primeDepth _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n+1) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n := by
  have hh := _root_.ThreeSum1960614.Machine.ThreeSum.Scales.primeDepth_upper _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix hR
  have hp : (4*_root_.ThreeSum.Scales.primeWindow n)^_root_.ThreeSum.Scales.primeDepth _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n ≤ _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n := by omega
  rw [pow_succ]
  exact Nat.mul_le_mul hp (Nat.le_self_pow (by decide : (2 : ℕ) ≠ 0) _)











end ThreeSum.BandPrimeScales

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Bounded finite index types for the same physical owner products

The A type is the complete flattened incidence array; B and C are the
retained sorted arrays. Coordinate transport is injective and preserves
both each owner's product and its exact weighted collision score.
-/

namespace ThreeSum.BandRawA
open _root_.ThreeSum.BandRawA


open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
open _root_.Finset
open scoped _root_.BigOperators

set_option maxHeartbeats 2000000
set_option maxRecDepth 8000











theorem coordinates_injective {a b c : ℕ} :
    Function.Injective (@_root_.ThreeSum.BandRawA.coordinates a b c) := by
  rintro ⟨i,j,k⟩ ⟨i',j',k'⟩ he
  simp only [_root_.ThreeSum.BandRawA.coordinates,Prod.mk.injEq] at he
  exact Prod.ext (Fin.ext he.1) (Prod.ext (Fin.ext he.2.1) (Fin.ext he.2.2))







@[simp] theorem mem_finiteAllProducts {nA nB nC g : ℕ} {rs : List _root_.ThreeSum.BandCandidateRows.Record}
    {t : Fin (_root_.ThreeSum.BandRawA.items nA g rs).length × Fin nB × Fin nC} :
    t ∈ _root_.ThreeSum.BandRawA.finiteAllProducts nA nB nC g rs ↔
      _root_.ThreeSum.BandRawA.coordinates t ∈ _root_.ThreeSum.BandRawA.allProducts nA nB nC g rs := by
  simp only [_root_.ThreeSum.BandRawA.finiteAllProducts,mem_filter,mem_univ,true_and]





theorem allProducts_bounds {nA nB nC g : ℕ} {rs : List _root_.ThreeSum.BandCandidateRows.Record} {t : ℕ × ℕ × ℕ}
    (ht : t ∈ _root_.ThreeSum.BandRawA.allProducts nA nB nC g rs) :
    t.1 < (_root_.ThreeSum.BandRawA.items nA g rs).length ∧ t.2.1 < nB ∧ t.2.2 < nC := by
  obtain ⟨ha,hb,hc⟩ := _root_.ThreeSum.BandRawA.mem_allProducts.mp ht
  exact ⟨ha,_root_.ThreeSum.BandRawA.bandPositions_lt hb,_root_.ThreeSum.BandRawA.bandPositions_lt hc⟩



theorem finite_lift {nA nB nC g : ℕ} {rs : List _root_.ThreeSum.BandCandidateRows.Record} {t : ℕ × ℕ × ℕ}
    (ht : t ∈ _root_.ThreeSum.BandRawA.allProducts nA nB nC g rs) :
    ∃ u ∈ _root_.ThreeSum.BandRawA.finiteAllProducts nA nB nC g rs, _root_.ThreeSum.BandRawA.coordinates u=t := by
  obtain ⟨ha,hb,hc⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.allProducts_bounds ht
  refine ⟨(⟨t.1,ha⟩,⟨t.2.1,hb⟩,⟨t.2.2,hc⟩),?_,rfl⟩
  exact _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.mem_finiteAllProducts.mpr ht



theorem sum_finiteAllProducts (F : (ℕ × ℕ × ℕ) → ℕ) (nA nB nC g : ℕ)
    (rs : List _root_.ThreeSum.BandCandidateRows.Record) :
    (∑ u ∈ _root_.ThreeSum.BandRawA.finiteAllProducts nA nB nC g rs, F (_root_.ThreeSum.BandRawA.coordinates u))=
      ∑ t ∈ _root_.ThreeSum.BandRawA.allProducts nA nB nC g rs, F t := by
  refine sum_bij (fun u _ => _root_.ThreeSum.BandRawA.coordinates u) ?_ ?_ ?_ ?_
  · intro u hu
    exact _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.mem_finiteAllProducts.mp hu
  · intro u hu v hv he
    exact _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.coordinates_injective he
  · intro t ht
    obtain ⟨u,hu,he⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.finite_lift ht
    exact ⟨u,hu,he⟩
  · intro u hu
    rfl



theorem finiteAll_weightedFalseCount (primes : ℕ → ℕ) (aux q nA nB nC g : ℕ)
    (A B C : ℕ → ℤ) (rs : List _root_.ThreeSum.BandCandidateRows.Record) :
    _root_.ThreeSum.Arithmetic.weightedFalseCount (_root_.ThreeSum.BandRawA.finiteAllProducts nA nB nC g rs)
      (fun t => C t.2.2.val-B t.2.1.val-_root_.ThreeSum.BandRawA.valueAt nA g rs A t.1.val)
      (_root_.ThreeSum.Auxiliary.moduli (_root_.ThreeSum.WeightedScore.auxiliarySet primes aux)) q=
      _root_.ThreeSum.BandWeightedScore.score primes aux q nA nB nC g A B C rs := by
  rw [← _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.all_weightedFalseCount primes aux q nA nB nC g A B C rs]
  unfold _root_.ThreeSum.Arithmetic.weightedFalseCount
  exact _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.sum_finiteAllProducts
    (fun t => if (q : ℤ) ∣ _root_.ThreeSum.ModuloCounts.difference (_root_.ThreeSum.BandRawA.valueAt nA g rs A) B C t then
      _root_.ThreeSum.Arithmetic.missWeight (_root_.ThreeSum.Auxiliary.moduli (_root_.ThreeSum.WeightedScore.auxiliarySet primes aux))
        (_root_.ThreeSum.ModuloCounts.difference (_root_.ThreeSum.BandRawA.valueAt nA g rs A) B C t) else 0) nA nB nC g rs





end ThreeSum.BandRawA

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Retained common-prime metadata for one actual color execution -/

namespace ThreeSum.EncodedColorPrimeData
open _root_.ThreeSum.EncodedColorPrimeData


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light









theorem Stored.heads_read {μ : ℕ → ℤ} {free M y : ℕ} {qs : ℕ → ℕ} (H : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeData.Stored μ free M y qs) :
    μ free=(qs (_root_.ThreeSum.LightBandPrimeDepth.depth M y) : ℤ) ∧
    μ (free+1)=(_root_.ThreeSum.LightBandPrimeDepth.depth M y : ℤ) ∧
    μ (free+2)=(_root_.ThreeSum.EncodedColorPrimeData.nextFree free M y : ℤ) ∧
    μ (free+3)=(_root_.ThreeSum.EncodedColorPrimeData.poolBase free : ℤ) ∧
    μ (free+4)=(_root_.ThreeSum.LightPrimePool.size y : ℤ) ∧
    μ (free+5)=(_root_.ThreeSum.EncodedColorPrimeData.prefixBase free y : ℤ) := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · simpa [_root_.ThreeSum.EncodedColorPrimeData.values] using H.header.getD (i := 0) (by simp [_root_.ThreeSum.EncodedColorPrimeData.values]) 0
  · simpa [_root_.ThreeSum.EncodedColorPrimeData.values] using H.header.getD (i := 1) (by simp [_root_.ThreeSum.EncodedColorPrimeData.values]) 0
  · simpa [_root_.ThreeSum.EncodedColorPrimeData.values] using H.header.getD (i := 2) (by simp [_root_.ThreeSum.EncodedColorPrimeData.values]) 0
  · simpa [_root_.ThreeSum.EncodedColorPrimeData.values] using H.header.getD (i := 3) (by simp [_root_.ThreeSum.EncodedColorPrimeData.values]) 0
  · simpa [_root_.ThreeSum.EncodedColorPrimeData.values] using H.header.getD (i := 4) (by simp [_root_.ThreeSum.EncodedColorPrimeData.values]) 0
  · simpa [_root_.ThreeSum.EncodedColorPrimeData.values] using H.header.getD (i := 5) (by simp [_root_.ThreeSum.EncodedColorPrimeData.values]) 0



end ThreeSum.EncodedColorPrimeData

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # One compact retained layout for a selected color -/

namespace ThreeSum.EncodedColorLayout
open _root_.ThreeSum.EncodedColorLayout





















theorem normalized_ends_before_count (free n g : ℕ) :
    _root_.ThreeSum.EncodedColorLayout.av free n+n ≤ _root_.ThreeSum.EncodedColorLayout.normalizedEnd free n g ∧ _root_.ThreeSum.EncodedColorLayout.ae free n+2+2*n ≤ _root_.ThreeSum.EncodedColorLayout.normalizedEnd free n g ∧
    _root_.ThreeSum.EncodedColorLayout.bv free n+n ≤ _root_.ThreeSum.EncodedColorLayout.normalizedEnd free n g ∧ _root_.ThreeSum.EncodedColorLayout.be free n+2+2*n ≤ _root_.ThreeSum.EncodedColorLayout.normalizedEnd free n g ∧
    _root_.ThreeSum.EncodedColorLayout.cv free n+n ≤ _root_.ThreeSum.EncodedColorLayout.normalizedEnd free n g ∧ _root_.ThreeSum.EncodedColorLayout.ce free n+2+2*n ≤ _root_.ThreeSum.EncodedColorLayout.normalizedEnd free n g ∧
    _root_.ThreeSum.EncodedColorLayout.tables free n+_root_.ThreeSum.ColorBandBounds.count n g ≤ _root_.ThreeSum.EncodedColorLayout.normalizedEnd free n g ∧
    _root_.ThreeSum.EncodedColorLayout.rec free n g+4*_root_.ThreeSum.ColorBandBounds.count n g ≤ _root_.ThreeSum.EncodedColorLayout.normalizedEnd free n g := by
  unfold _root_.ThreeSum.EncodedColorLayout.normalizedEnd _root_.ThreeSum.LightBandRawA.space _root_.ThreeSum.LightBandRawA.positionBase _root_.ThreeSum.LightBandRawA.ownerBase
    _root_.ThreeSum.LightBandRawA.capacity _root_.ThreeSum.EncodedColorLayout.vals _root_.ThreeSum.EncodedColorLayout.rec _root_.ThreeSum.EncodedColorLayout.tables _root_.ThreeSum.EncodedColorLayout.ce _root_.ThreeSum.EncodedColorLayout.cv _root_.ThreeSum.EncodedColorLayout.be _root_.ThreeSum.EncodedColorLayout.bv _root_.ThreeSum.EncodedColorLayout.ae _root_.ThreeSum.EncodedColorLayout.av
  omega







theorem prime_le_cover (free n g M y : ℕ) : _root_.ThreeSum.EncodedColorLayout.prime free n g+6 ≤ _root_.ThreeSum.EncodedColorLayout.cover free n g M y := by
  unfold _root_.ThreeSum.EncodedColorLayout.cover _root_.ThreeSum.EncodedColorPrimeData.nextFree _root_.ThreeSum.EncodedColorPrimeData.prefixBase _root_.ThreeSum.EncodedColorPrimeData.poolBase
  omega

theorem normalized_ends_cover (free n g M y : ℕ) :
    _root_.ThreeSum.EncodedColorLayout.av free n+n ≤ _root_.ThreeSum.EncodedColorLayout.cover free n g M y ∧ _root_.ThreeSum.EncodedColorLayout.ae free n+2+2*n ≤ _root_.ThreeSum.EncodedColorLayout.cover free n g M y ∧
    _root_.ThreeSum.EncodedColorLayout.bv free n+n ≤ _root_.ThreeSum.EncodedColorLayout.cover free n g M y ∧ _root_.ThreeSum.EncodedColorLayout.be free n+2+2*n ≤ _root_.ThreeSum.EncodedColorLayout.cover free n g M y ∧
    _root_.ThreeSum.EncodedColorLayout.cv free n+n ≤ _root_.ThreeSum.EncodedColorLayout.cover free n g M y ∧ _root_.ThreeSum.EncodedColorLayout.ce free n+2+2*n ≤ _root_.ThreeSum.EncodedColorLayout.cover free n g M y ∧
    _root_.ThreeSum.EncodedColorLayout.tables free n+_root_.ThreeSum.ColorBandBounds.count n g ≤ _root_.ThreeSum.EncodedColorLayout.cover free n g M y ∧
    _root_.ThreeSum.EncodedColorLayout.rec free n g+4*_root_.ThreeSum.ColorBandBounds.count n g ≤ _root_.ThreeSum.EncodedColorLayout.cover free n g M y ∧
    _root_.ThreeSum.LightBandRawA.space (_root_.ThreeSum.EncodedColorLayout.vals free n g) (_root_.ThreeSum.ColorBandBounds.count n g) g ≤ _root_.ThreeSum.EncodedColorLayout.cover free n g M y := by
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorLayout.normalized_ends_before_count free n g
  have h := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorLayout.prime_le_cover free n g M y
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _root_.ThreeSum.EncodedColorLayout.normalizedEnd free n g ≤ _
  unfold _root_.ThreeSum.EncodedColorLayout.prime at h
  omega

end ThreeSum.EncodedColorLayout

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The executed common-prime stage at the actual integer schedule

This interface consumes the physical records produced by the band catalog.
It derives every flag, band-start and candidate-count premise from that
catalog, computes the depth and pool, and returns the arithmetic guard and
the finite physical-domain false-mass bound at the actual execution cost.
-/

namespace ThreeSum.LightBandPrimeStage
open _root_.ThreeSum.LightBandPrimeStage


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandEnumeration
open _root_.ThreeSum1960614.Machine.ThreeSum.BandEnumeration
open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000





theorem records_valid {A B C : _root_.ThreeSum.BandEnumeration.Family} {nA nB nC g : ℕ}
    (hA : A.size=_root_.ThreeSum.BandPartition.size nA g)
    (hB : B.size=_root_.ThreeSum.BandPartition.size nB g)
    (hC : C.size=_root_.ThreeSum.BandPartition.size nC g) (hg : 0 < g) :
    ∀ r ∈ _root_.ThreeSum.BandCandidateRows.records A B C, r.flag=1 → r.a*g ≤ nA ∧ r.b*g ≤ nB ∧ r.c*g ≤ nC := by
  intro r hr hf
  obtain ⟨ha,hb,hc,_⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows.records_sound hr hf
  rw [hA] at ha
  rw [hB] at hb
  rw [hC] at hc
  exact ⟨(_root_.ThreeSum.BandPartition.start_lt hg ha).le,(_root_.ThreeSum.BandPartition.start_lt hg hb).le,
    (_root_.ThreeSum.BandPartition.start_lt hg hc).le⟩





variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {d : ℕ} {μ : ℕ → ℤ}
    {a b c n nA nB nC k recs free : ℕ}



end ThreeSum.LightBandPrimeStage

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Construct the dense-stop threshold from actual cover and source records

The host computes the representation cap, recomputes the exact aggregate
weighted score at the selected common modulus, multiplies the two, and
initializes the running counter. The four retained cells are counter,
threshold, representation cap and weighted score. Scratch starts after them.
-/

namespace ThreeSum.LightDenseSetup
open _root_.ThreeSum.LightDenseSetup


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows

set_option maxHeartbeats 2200000
set_option maxRecDepth 10000

















theorem falseScore_eq (primes : ℕ → ℕ) (s q nA nB nC g : ℕ)
    (A B C : ℕ → ℤ) (rs : List _root_.ThreeSum.BandCandidateRows.Record) :
    _root_.ThreeSum.LightDenseSetup.falseScore primes s q nA nB nC g A B C rs=
      _root_.ThreeSum.BandWeightedScore.score primes s q nA nB nC g A B C rs :=
  _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.finiteAll_weightedFalseCount primes s q nA nB nC g A B C rs

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {d : ℕ} {μ : ℕ → ℤ}
    {a b c nA nB nC g recs q aux s cover free maxMod U h J : ℕ}



end ThreeSum.LightDenseSetup

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Concrete source inputs from the retained normalization and wanted outputs -/

namespace ThreeSum.SourceFiniteInputs
open _root_.ThreeSum.SourceFiniteInputs


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule










theorem prepared_read {μ : ℕ → ℤ} {values endpoints g : ℕ} {hg : 0 < g}
    {original L : List ℤ} {hs : L.Pairwise (· < ·)}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.LightBandPreprocessing.Represents μ values endpoints g hg original L hs) :
    ∀ j < L.length, μ (values+j)=L.getD j 0 := fun j hj => H.1.getD hj 0

theorem prepared_headers {μ : ℕ → ℤ} {values endpoints g : ℕ} {hg : 0 < g}
    {original L : List ℤ} {hs : L.Pairwise (· < ·)}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.LightBandPreprocessing.Represents μ values endpoints g hg original L hs) :
    μ endpoints=(L.length : ℤ) ∧ μ (endpoints+1)=(_root_.ThreeSum.BandPartition.size L.length g : ℤ) :=
  ⟨H.2.2.2.1,H.2.2.2.2.1⟩

theorem prepared_bound {μ : ℕ → ℤ} {values endpoints g U : ℕ} {hg : 0 < g}
    {original L : List ℤ} {hs : L.Pairwise (· < ·)}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.LightBandPreprocessing.Represents μ values endpoints g hg original L hs)
    (hb : ∀ z ∈ original, |z| ≤ (U : ℤ)) :
    ∀ j < L.length, |L.getD j 0| ≤ (U : ℤ) := by
  intro j hj
  rw [List.getD_eq_getElem _ _ hj]
  exact hb _ ((H.2.2.1 _).mp (List.getElem_mem hj))







end ThreeSum.SourceFiniteInputs

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Actual finite budgets of the retained common-prime stage -/

namespace ThreeSum.EncodedColorPrimeCosts
open _root_.ThreeSum.EncodedColorPrimeCosts


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open _root_.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds







theorem count_mono {nA nB nC nA' nB' nC' g : ℕ} (ha : nA ≤ nA') (hb : nB ≤ nB') (hc : nC ≤ nC') :
    _root_.ThreeSum.LightEncodedColorPrime.count nA nB nC g ≤ _root_.ThreeSum.LightEncodedColorPrime.count nA' nB' nC' g := by
  have a := _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition.size_mono (g := g) ha
  have b := _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition.size_mono (g := g) hb
  have c := _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition.size_mono (g := g) hc
  unfold _root_.ThreeSum.LightEncodedColorPrime.count
  exact Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul b c) (Nat.mul_le_mul a b)) (Nat.mul_le_mul a c)









theorem moduli_pos {A B C : List ℤ} {g y : ℕ} {hg : 0 < g}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (hy : 0 < y) (i : ℕ) : 0 < _root_.ThreeSum.LightEncodedColorPrime.moduli A B C g hg hsA hsB hsC y i :=
  _root_.ThreeSum1960614.Machine.ThreeSum.BandPrimeChoice.modulus_pos (_root_.ThreeSum.LightPrimePool.prime y)
    (fun j => A.getD j 0) (fun j => B.getD j 0) (fun j => C.getD j 0)
    (_root_.ThreeSum.BandRawA.sortedRecords A B C g hg hsA hsB hsC) (_root_.ThreeSum1960614.Machine.ThreeSum.LightPrimePool.size_pos hy)
    (fun j hj => (_root_.ThreeSum1960614.Machine.ThreeSum.LightPrimePool.prime_spec hj).1) i

theorem scheduled_modulus_eq (n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) :
    _root_.ThreeSum.LightEncodedColorPrime.moduli A B C (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize_pos n) hsA hsB hsC (_root_.ThreeSum.Scales.primeWindow n)
      (_root_.ThreeSum.LightBandPrimeDepth.depth (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) (_root_.ThreeSum.Scales.primeWindow n))=
      _root_.ThreeSum1960614.Machine.ThreeSum.BandPrimeScales.modulus n A.length B.length C.length
        (fun j => A.getD j 0) (fun j => B.getD j 0) (fun j => C.getD j 0)
        (_root_.ThreeSum.BandRawA.sortedRecords A B C (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize_pos n) hsA hsB hsC) := rfl

theorem scheduled_modulus_guard {n : ℕ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (hR : 4 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) :
    4*_root_.ThreeSum.LightEncodedColorPrime.moduli A B C (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize_pos n) hsA hsB hsC (_root_.ThreeSum.Scales.primeWindow n)
      (_root_.ThreeSum.LightBandPrimeDepth.depth (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) (_root_.ThreeSum.Scales.primeWindow n)) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeCosts.scheduled_modulus_eq]
  exact _root_.ThreeSum1960614.Machine.ThreeSum.BandPrimeScales.modulus_guard _ _ _ _ hR

end ThreeSum.EncodedColorPrimeCosts

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Retained normalized pointers and the actual incidence-count cell -/

namespace ThreeSum.EncodedColorNormalizedData
open _root_.ThreeSum.EncodedColorNormalizedData


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.ColorClassLists
open _root_.ThreeSum1960614.Machine.ThreeSum.ColorClassLists
open _root_.ThreeSum.BandRawA
open _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA
open _root_.ThreeSum.EncodedColorLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorLayout





theorem records_length_le {A B C : List ℤ} {g n : ℕ} {hg : 0 < g}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (ha : A.length ≤ n) (hb : B.length ≤ n) (hc : C.length ≤ n) :
    (_root_.ThreeSum.BandRawA.sortedRecords A B C g hg hsA hsB hsC).length ≤ _root_.ThreeSum.ColorBandBounds.count n g := by
  have h := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeCosts.count_mono (g := g) ha hb hc
  have hright : _root_.ThreeSum.LightEncodedColorPrime.count n n n g=_root_.ThreeSum.ColorBandBounds.count n g := by
    unfold _root_.ThreeSum.LightEncodedColorPrime.count _root_.ThreeSum.ColorBandBounds.count
    ring
  rw [hright] at h
  simp only [_root_.ThreeSum.BandRawA.sortedRecords, _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows.records_length]
  exact h





theorem heads_read {μ : ℕ → ℤ} {free n g : ℕ} (H : _root_.ThreeSum1960614.Machine.Light.Seg μ free (_root_.ThreeSum.EncodedColorLayout.normalizedHeads free n g)) :
    μ free=(_root_.ThreeSum.EncodedColorLayout.av free n : ℤ) ∧ μ (free+1)=(_root_.ThreeSum.EncodedColorLayout.ae free n : ℤ) ∧
    μ (free+2)=(_root_.ThreeSum.EncodedColorLayout.bv free n : ℤ) ∧ μ (free+3)=(_root_.ThreeSum.EncodedColorLayout.be free n : ℤ) ∧
    μ (free+4)=(_root_.ThreeSum.EncodedColorLayout.cv free n : ℤ) ∧ μ (free+5)=(_root_.ThreeSum.EncodedColorLayout.ce free n : ℤ) ∧
    μ (free+6)=(_root_.ThreeSum.EncodedColorLayout.rec free n g : ℤ) ∧ μ (free+7)=(_root_.ThreeSum.EncodedColorLayout.vals free n g : ℤ) := by
  have h (i : ℕ) (hi : i < 8) := H.getD (i := i) (by simpa [_root_.ThreeSum.EncodedColorLayout.normalizedHeads] using hi) 0
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa [_root_.ThreeSum.EncodedColorLayout.normalizedHeads] using h 0 (by omega)
  · simpa [_root_.ThreeSum.EncodedColorLayout.normalizedHeads] using h 1 (by omega)
  · simpa [_root_.ThreeSum.EncodedColorLayout.normalizedHeads] using h 2 (by omega)
  · simpa [_root_.ThreeSum.EncodedColorLayout.normalizedHeads] using h 3 (by omega)
  · simpa [_root_.ThreeSum.EncodedColorLayout.normalizedHeads] using h 4 (by omega)
  · simpa [_root_.ThreeSum.EncodedColorLayout.normalizedHeads] using h 5 (by omega)
  · simpa [_root_.ThreeSum.EncodedColorLayout.normalizedHeads] using h 6 (by omega)
  · simpa [_root_.ThreeSum.EncodedColorLayout.normalizedHeads] using h 7 (by omega)

end ThreeSum.EncodedColorNormalizedData

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # The same normalized finite witnesses and their actually selected prime -/

namespace ThreeSum.EncodedColorPrimeReadyData
open _root_.ThreeSum.EncodedColorPrimeReadyData


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.ColorClassLists
open _root_.ThreeSum1960614.Machine.ThreeSum.ColorClassLists
open _root_.ThreeSum.EncodedColorLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData







theorem selected_pos {n : ℕ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)} :
    0 < _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC :=
  _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeCosts.moduli_pos (lt_of_lt_of_le (by decide : 0 < 2) (_root_.ThreeSum.Scales.primeWindow_ge_two n)) _

theorem selected_guard {n : ℕ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (hR : 4 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) : 4*_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC ≤ _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n :=
  _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeCosts.scheduled_modulus_guard hR

end ThreeSum.EncodedColorPrimeReadyData

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Keep the complete selected-color payload while later stages extend memory -/

namespace ThreeSum.EncodedColorPipelineData
open _root_.ThreeSum.EncodedColorPipelineData


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.ColorClassLists
open _root_.ThreeSum1960614.Machine.ThreeSum.ColorClassLists
open _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData

set_option maxHeartbeats 1400000
set_option maxRecDepth 10000

theorem Stored.heads_read {μ : ℕ → ℤ} {free n : ℕ} {color : _root_.ThreeSum.Coloring.Parameter (_root_.ThreeSum.Scales.inputBits n+1)}
    {x : Fin n → ℤ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC) :
    let out := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC
    μ out=(_root_.ThreeSum.EncodedColorLayout.prime free n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) : ℤ) ∧
    μ (out+1)=(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.coverBase free n : ℤ) ∧
    μ (out+2)=(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.wantedHeader free n (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData.incidences n A B C hsA hsB hsC).length : ℤ) ∧
    μ (out+3)=(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.controls free n A B C hsA hsB hsC : ℤ) ∧
    μ (out+4)=(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.bankHeader free n A B C hsA hsB hsC : ℤ) ∧
    μ (out+5)=(out+8 : ℕ) ∧
    μ (out+6)=((_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData.incidences n A B C hsA hsB hsC).length : ℤ) ∧
    μ (out+7)=(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC : ℤ) := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa [_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.values,_root_.ThreeSum.LightEncodedColorResult.values] using H.heads.getD (i := 0) (by simp [_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.values,_root_.ThreeSum.LightEncodedColorResult.values]) 0
  · simpa [_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.values,_root_.ThreeSum.LightEncodedColorResult.values] using H.heads.getD (i := 1) (by simp [_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.values,_root_.ThreeSum.LightEncodedColorResult.values]) 0
  · simpa [_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.values,_root_.ThreeSum.LightEncodedColorResult.values] using H.heads.getD (i := 2) (by simp [_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.values,_root_.ThreeSum.LightEncodedColorResult.values]) 0
  · simpa [_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.values,_root_.ThreeSum.LightEncodedColorResult.values] using H.heads.getD (i := 3) (by simp [_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.values,_root_.ThreeSum.LightEncodedColorResult.values]) 0
  · simpa [_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.values,_root_.ThreeSum.LightEncodedColorResult.values] using H.heads.getD (i := 4) (by simp [_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.values,_root_.ThreeSum.LightEncodedColorResult.values]) 0
  · simpa [_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.values,_root_.ThreeSum.LightEncodedColorResult.values] using H.heads.getD (i := 5) (by simp [_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.values,_root_.ThreeSum.LightEncodedColorResult.values]) 0
  · simpa [_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.values,_root_.ThreeSum.LightEncodedColorResult.values] using H.heads.getD (i := 6) (by simp [_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.values,_root_.ThreeSum.LightEncodedColorResult.values]) 0
  · simpa [_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.values,_root_.ThreeSum.LightEncodedColorResult.values] using H.heads.getD (i := 7) (by simp [_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.values,_root_.ThreeSum.LightEncodedColorResult.values]) 0





end ThreeSum.EncodedColorPipelineData

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Uniform budgets for wanted records followed by the shared source banks -/

namespace ThreeSum.EncodedColorStageCosts
open _root_.ThreeSum.EncodedColorStageCosts


open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds































theorem selected_le_maxMod {n : ℕ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (hR : 4 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC ≤ _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n := by
  have hp := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeReadyData.selected_guard (A := A) (B := B) (C := C)
    (hsA := hsA) (hsB := hsB) (hsC := hsC) hR
  have hy := _root_.ThreeSum.Scales.primeWindow_ge_two n
  have hm : _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n ≤ _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n := by
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod
    exact Nat.le_mul_of_pos_right _ (by positivity)
  omega

end ThreeSum.EncodedColorStageCosts

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

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
open _root_.ThreeSum.ThreeSumColorBudgets


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.ColorClassLists
open _root_.ThreeSum1960614.Machine.ThreeSum.ColorClassLists
open _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData

set_option maxHeartbeats 2200000
set_option maxRecDepth 12000





variable {μ : ℕ → ℤ} {free n : ℕ}
    {color : _root_.ThreeSum.Coloring.Parameter (_root_.ThreeSum.Scales.inputBits n+1)} {x : Fin n → ℤ}
    {A B C : List ℤ} {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}

theorem normalized_lengths (H : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC) :
    A.length ≤ n ∧ B.length ≤ n ∧ C.length ≤ n :=
  ⟨H.normalized.2.1.2.1.trans (_root_.ThreeSum1960614.Machine.ThreeSum.ColorClassLists.length_classList_le color x 0 1),
    H.normalized.2.2.1.2.1.trans (_root_.ThreeSum1960614.Machine.ThreeSum.ColorClassLists.length_classList_le color x 1 1),
    H.normalized.2.2.2.1.2.1.trans (_root_.ThreeSum1960614.Machine.ThreeSum.ColorClassLists.length_classList_le color x 2 (-1))⟩

theorem normalized_values {U : ℕ}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (hx : ∀ i, |x i| ≤ (U : ℤ)) :
    (∀ j < A.length, |A.getD j 0| ≤ (U : ℤ)) ∧
      (∀ j < B.length, |B.getD j 0| ≤ (U : ℤ)) ∧
      (∀ j < C.length, |C.getD j 0| ≤ (U : ℤ)) :=
  ⟨_root_.ThreeSum1960614.Machine.ThreeSum.SourceFiniteInputs.prepared_bound H.normalized.2.1
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightColorBands.class_bounded color x 0 1 (by norm_num) hx),
    _root_.ThreeSum1960614.Machine.ThreeSum.SourceFiniteInputs.prepared_bound H.normalized.2.2.1
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightColorBands.class_bounded color x 1 1 (by norm_num) hx),
    _root_.ThreeSum1960614.Machine.ThreeSum.SourceFiniteInputs.prepared_bound H.normalized.2.2.2.1
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightColorBands.class_bounded color x 2 (-1) (by norm_num) hx)⟩















open _root_.Filter



end ThreeSum.ThreeSumColorBudgets

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Exact retained addresses for reporting one encoded original color -/

namespace ThreeSum.ThreeSumReportingSetupData
open _root_.ThreeSum.ThreeSumReportingSetupData


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData















theorem prefix_le_report (free n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) :
    free+8 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.reportBase free n A B C hsA hsB hsC ∧
    _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.coverBase free n ≤ _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.reportBase free n A B C hsA hsB hsC := by
  obtain ⟨_,hf,hc,_,hs,_⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.ordered free n A B C hsA hsB hsC
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.reportBase
  omega

theorem cover_end_le_report (free n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeyData.keyEnd (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.coverBase free n)
      (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.reportBase free n A B C hsA hsB hsC := by
  obtain ⟨_,_,_,hw,hs,_⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.ordered free n A B C hsA hsB hsC
  have he : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.wantedHeader free n (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData.incidences n A B C hsA hsB hsC).length=
      _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeyData.keyEnd (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.coverBase free n)
        (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n))+3*(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData.incidences n A B C hsA hsB hsC).length := rfl
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.reportBase
  omega

theorem pool_end_le_report (free n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) :
    _root_.ThreeSum.EncodedColorPrimeData.poolBase (_root_.ThreeSum.EncodedColorLayout.prime free n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n))+
      _root_.ThreeSum.LightPrimePool.size (_root_.ThreeSum.Scales.primeWindow n) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.reportBase free n A B C hsA hsB hsC := by
  have hp := (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.prefix_le_report free n A B C hsA hsB hsC).2
  have hs := _root_.ThreeSum1960614.Machine.ThreeSum.LightPrimePool.size_le (_root_.ThreeSum.Scales.primeWindow n)
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.coverBase _root_.ThreeSum.EncodedColorLayout.cover
    _root_.ThreeSum.EncodedColorPrimeData.nextFree _root_.ThreeSum.EncodedColorPrimeData.prefixBase at hp
  omega

end ThreeSum.ThreeSumReportingSetupData

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Initialize the actual dense counter using the retained original arrays -/

namespace ThreeSum.LightThreeSumReportingSetupDense
open _root_.ThreeSum.LightThreeSumReportingSetupDense


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open _root_.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData
open _root_.ThreeSum.BandPartition
open _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition
open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
open _root_.ThreeSum.BandRawA
open _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA

set_option maxHeartbeats 2600000
set_option maxRecDepth 16000













theorem dense_word_le {n nA nB nC R U : ℕ}
    (hA : nA ≤ n) (hB : nB ≤ n) (hC : nC ≤ n) (hR : R ≤ _root_.ThreeSum.ColorBandBounds.count n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightDenseSetup.word (_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n) nA nB nC (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) R
      (_root_.ThreeSum.LightPrimePool.size (_root_.ThreeSum.Scales.primeWindow n)) U (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumReportingSetupDense.word n U := by
  apply le_trans (b := _root_.ThreeSum1960614.Machine.ThreeSum.LightDenseSetup.word (_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n) n n n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)
    (_root_.ThreeSum.ColorBandBounds.count n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)) (_root_.ThreeSum.LightPrimePool.size (_root_.ThreeSum.Scales.primeWindow n)) U
    (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)))
  · unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightDenseSetup.word _root_.ThreeSum.LightBandWeightedScore.word _root_.ThreeSum.LightBandWeightedScoreCell.word
    gcongr
  · unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumReportingSetupDense.word
    omega





end ThreeSum.LightThreeSumReportingSetupDense

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumReportingSetupDense

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open _root_.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData
open _root_.ThreeSum.BandPartition
open _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition
open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
open _root_.ThreeSum.BandRawA
open _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA
set_option maxHeartbeats 2600000
set_option maxRecDepth 16000
section

theorem ThreeSum1960614.Machine.ThreeSum.LightThreeSumReportingSetupDense.program_meets__implementation_2771687098 {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {d : ℕ} {μ : ℕ → ℤ} {free n params U dst : ℕ}
    {color : _root_.ThreeSum.Coloring.Parameter (_root_.ThreeSum.Scales.inputBits n+1)} {x : Fin n → ℤ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (Hparams : _root_.ThreeSum1960614.Machine.Light.Seg μ params (_root_.ThreeSum1960614.Machine.ThreeSum.LightParameterInit.values n)) (hparams : params+19 ≤ free)
    (hw : (lim.space : ℤ) ≤ lim.word) (hR : 4 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n)
    (hprior : _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.reportBase free n A B C hsA hsB hsC ≤ dst)
    (hspace : _root_.ThreeSum.LightWeightedScore.space (dst+4) (_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n) (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) U ≤ lim.space)
    (hword : (_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumReportingSetupDense.word n U : ℤ) ≤ lim.word)
    (hdepth : d+Nat.clog 2 (_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n)+8 ≤ lim.depth)
    (hx : ∀ i, |x i| ≤ (U : ℤ)) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumReportingSetupDense.program 20 d
      [n,params,free,_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC,dst] μ
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumReportingSetupDense.time n U (_root_.ThreeSum.BandRawA.sortedRecords A B C (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize_pos n) hsA hsB hsC).length)
      (fun r ν => r=(dst : ℤ) ∧
        _root_.ThreeSum.LightDenseSetup.Stored ν dst
          (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.representationCap (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)))
          (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumColorBudgets.falseScore n A B C hsA hsB hsC) ∧
        _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.Stored ν free n color x A B C hsA hsB hsC ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ ν dst) := by
  let out := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC
  let primeHeader := _root_.ThreeSum.EncodedColorLayout.prime free n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)
  let cover := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.coverBase free n
  let p := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC
  let av := _root_.ThreeSum.EncodedColorLayout.av free n
  let ae := _root_.ThreeSum.EncodedColorLayout.ae free n
  let bv := _root_.ThreeSum.EncodedColorLayout.bv free n
  let be := _root_.ThreeSum.EncodedColorLayout.be free n
  let cv := _root_.ThreeSum.EncodedColorLayout.cv free n
  let ce := _root_.ThreeSum.EncodedColorLayout.ce free n
  let recs := _root_.ThreeSum.EncodedColorLayout.rec free n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)
  let rs := _root_.ThreeSum.BandRawA.sortedRecords A B C (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize_pos n) hsA hsB hsC
  let g := _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n
  let J := _root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)
  let aux := _root_.ThreeSum.EncodedColorPrimeData.poolBase primeHeader
  let s := _root_.ThreeSum.LightPrimePool.size (_root_.ThreeSum.Scales.primeWindow n)
  have hdst : dst+4 ≤ lim.space := by
    have hh := (le_max_right _ _).trans hspace
    change dst+4+(Nat.log 2 (_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n+1)+2) ≤ lim.space at hh
    omega
  obtain ⟨hnA,hnB,hnC⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumColorBudgets.normalized_lengths H
  have hrecords := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData.records_length_le (g := g) (hg := _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize_pos n)
    (hsA := hsA) (hsB := hsB) (hsC := hsC) hnA hnB hnC
  change rs.length ≤ _root_.ThreeSum.ColorBandBounds.count n g at hrecords
  have hrs : rs.length=_root_.ThreeSum.LightEncodedColorPrime.count A.length B.length C.length g := by
    simp only [rs,_root_.ThreeSum.BandRawA.sortedRecords,_root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows.records_length]
    rfl
  have hbound (z : ℕ) (hz : z ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumReportingSetupDense.word n U) : (z : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hz).trans hword
  have hnWord := hbound n (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumReportingSetupDense.word; omega)
  have hgWord := hbound g (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumReportingSetupDense.word; omega)
  have hJWord := hbound J (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumReportingSetupDense.word; omega)
  have hPWord := hbound (_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n) (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumReportingSetupDense.word; omega)
  have hsWord := hbound s (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumReportingSetupDense.word; omega)
  have hcountWord := hbound rs.length (hrecords.trans (by
    change _root_.ThreeSum.ColorBandBounds.count n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumReportingSetupDense.word n U
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumReportingSetupDense.word
    omega))
  have hDenseWord := hbound _ (_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumReportingSetupDense.dense_word_le hnA hnB hnC hrecords)
  have hpmax : p ≤ _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorStageCosts.selected_le_maxMod hR
  have hpWord : (p : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hpmax).trans hPWord
  have hGA := _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition.size_le A.length g
  have hGB := _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition.size_le B.length g
  have hGC := _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition.size_le C.length g
  have hcountZ : (_root_.ThreeSum.BandPartition.size B.length g : ℤ)*(_root_.ThreeSum.BandPartition.size C.length g : ℤ)+
      (_root_.ThreeSum.BandPartition.size A.length g : ℤ)*(_root_.ThreeSum.BandPartition.size B.length g : ℤ)+(_root_.ThreeSum.BandPartition.size A.length g : ℤ)*(_root_.ThreeSum.BandPartition.size C.length g : ℤ) ≤ lim.word := by
    simpa only [hrs,_root_.ThreeSum.LightEncodedColorPrime.count,Nat.cast_add,Nat.cast_mul] using hcountWord
  have hBC0 : (0 : ℤ) ≤ (_root_.ThreeSum.BandPartition.size B.length g : ℤ)*(_root_.ThreeSum.BandPartition.size C.length g : ℤ) := by positivity
  have hAB0 : (0 : ℤ) ≤ (_root_.ThreeSum.BandPartition.size A.length g : ℤ)*(_root_.ThreeSum.BandPartition.size B.length g : ℤ) := by positivity
  have hAC0 : (0 : ℤ) ≤ (_root_.ThreeSum.BandPartition.size A.length g : ℤ)*(_root_.ThreeSum.BandPartition.size C.length g : ℤ) := by positivity
  have hprefix := _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.prefix_le_report free n A B C hsA hsB hsC
  obtain ⟨hmeta,_,_,_,_,_⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.ordered free n A B C hsA hsB hsC
  change primeHeader+6 ≤ cover at hmeta
  have hcover : cover ≤ dst := hprefix.2.trans hprior
  have hfree : free+8 ≤ dst := hprefix.1.trans hprior
  have hout : out+8 ≤ dst := hprior
  have hkey := (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.cover_end_le_report free n A B C hsA hsB hsC).trans hprior
  have haux := (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.pool_end_le_report free n A B C hsA hsB hsC).trans hprior
  obtain ⟨hav,hae,hbv,hbe,hcv,hce,_,hrec,_⟩ :=
    _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorLayout.normalized_ends_cover free n g (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) (_root_.ThreeSum.Scales.primeWindow n)
  change av+n ≤ cover at hav
  change ae+2+2*n ≤ cover at hae
  change bv+n ≤ cover at hbv
  change be+2+2*n ≤ cover at hbe
  change cv+n ≤ cover at hcv
  change ce+2+2*n ≤ cover at hce
  change recs+4*_root_.ThreeSum.ColorBandBounds.count n g ≤ cover at hrec
  obtain ⟨readMeta,readCover,_,_,_,_,_,readP⟩ := H.heads_read
  change μ out=(primeHeader : ℤ) at readMeta
  change μ (out+1)=(cover : ℤ) at readCover
  change μ (out+7)=(p : ℤ) at readP
  obtain ⟨readA,readAE,readB,readBE,readC,readCE,readRecs,_⟩ :=
    _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData.heads_read H.normalizedHeads
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
  obtain ⟨_,_,readJ,_,_,readG,_⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorParameterData.reads Hparams
  change μ (params+3)=(J : ℤ) at readJ
  change μ (params+17)=(g : ℤ) at readG
  obtain ⟨readNA,readGA⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.SourceFiniteInputs.prepared_headers H.normalized.2.1
  obtain ⟨readNB,readGB⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.SourceFiniteInputs.prepared_headers H.normalized.2.2.1
  obtain ⟨readNC,readGC⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.SourceFiniteInputs.prepared_headers H.normalized.2.2.2.1
  change μ ae=(A.length : ℤ) at readNA
  change μ be=(B.length : ℤ) at readNB
  change μ ce=(C.length : ℤ) at readNC
  change μ (ae+1)=(_root_.ThreeSum.BandPartition.size A.length g : ℤ) at readGA
  change μ (be+1)=(_root_.ThreeSum.BandPartition.size B.length g : ℤ) at readGB
  change μ (ce+1)=(_root_.ThreeSum.BandPartition.size C.length g : ℤ) at readGC
  have hvalueA := _root_.ThreeSum1960614.Machine.ThreeSum.SourceFiniteInputs.prepared_read H.normalized.2.1
  have hvalueB := _root_.ThreeSum1960614.Machine.ThreeSum.SourceFiniteInputs.prepared_read H.normalized.2.2.1
  have hvalueC := _root_.ThreeSum1960614.Machine.ThreeSum.SourceFiniteInputs.prepared_read H.normalized.2.2.2.1
  obtain ⟨hA,hB,hC⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumColorBudgets.normalized_values H hx
  have hproduct : ∀ i < s, p*_root_.ThreeSum.LightPrimePool.prime (_root_.ThreeSum.Scales.primeWindow n) i ≤ _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n := by
    intro i hi
    have hp := (_root_.ThreeSum1960614.Machine.ThreeSum.BandPrimeScales.modulus_bounds n A.length B.length C.length
      (fun j => A.getD j 0) (fun j => B.getD j 0) (fun j => C.getD j 0) rs).2
    change p ≤ (4*_root_.ThreeSum.Scales.primeWindow n)^_root_.ThreeSum.Scales.primeDepth _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n at hp
    exact (Nat.mul_le_mul hp (_root_.ThreeSum1960614.Machine.ThreeSum.LightPrimePool.prime_spec hi).2.2).trans
      (by simpa only [← pow_succ] using _root_.ThreeSum1960614.Machine.ThreeSum.BandPrimeScales.resource_modulus_bound hR)
  have hread : ∀ i < s, μ (aux+i)=(_root_.ThreeSum.LightPrimePool.prime (_root_.ThreeSum.Scales.primeWindow n) i : ℤ) :=
    fun i hi => H.primes.pool.read hi
  have hflags : ∀ r ∈ rs, r.flag=0 ∨ r.flag=1 := fun _ hr => _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows.records_flag hr
  have hvalid : ∀ r ∈ rs, r.flag=1 → r.a*g ≤ A.length ∧ r.b*g ≤ B.length ∧ r.c*g ≤ C.length :=
    _root_.ThreeSum1960614.Machine.ThreeSum.LightBandPrimeStage.records_valid rfl rfl rfl (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize_pos n)
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
  change _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumReportingSetupDense.program 20 d [n,params,free,out,dst] μ (_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumReportingSetupDense.time n U rs.length) _
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body (p := 20) (by rfl : program[20]?=some (body 19))
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumReportingSetupDense.body _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumReportingSetupDense.time
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (primeHeader : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, readMeta]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [readMeta] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, readMeta] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (cover : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, readCover, out1]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [readCover, out1] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, readCover, out1] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (p : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, readP, out7]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [readP, out7] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, readP, out7] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (av : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, readA]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [readA] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, readA] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (ae : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, readAE, free1]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [readAE, free1] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, readAE, free1] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (bv : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, readB, free2]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [readB, free2] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, readB, free2] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (be : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, readBE, free3]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [readBE, free3] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, readBE, free3] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (cv : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, readC, free4]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [readC, free4] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, readC, free4] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (ce : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, readCE, free5]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [readCE, free5] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, readCE, free5] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (recs : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, readRecs, free6]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [readRecs, free6] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, readRecs, free6] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (A.length : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, readNA]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [readNA] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, readNA] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (B.length : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, readNB]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [readNB] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, readNB] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (C.length : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, readNC]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [readNC] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, readNC] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.BandPartition.size A.length g : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, readGA, ae1]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [readGA, ae1] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, readGA, ae1] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.BandPartition.size B.length g : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, readGB, be1]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [readGB, be1] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, readGB, be1] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.BandPartition.size C.length g : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, readGC, ce1]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [readGC, ce1] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, readGC, ce1] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (rs.length : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hrs, _root_.ThreeSum.LightEncodedColorPrime.count]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hrs, _root_.ThreeSum.LightEncodedColorPrime.count] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hrs, _root_.ThreeSum.LightEncodedColorPrime.count] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (g : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, readG, par17]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [readG, par17] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, readG, par17] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (J : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, readJ, par3]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [readJ, par3] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, readJ, par3] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (aux : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, readAux, prime3]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [readAux, prime3] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, readAux, prime3] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (s : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, readS, prime4]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [readS, prime4] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, readS, prime4] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  have hcall := (_root_.ThreeSum1960614.Machine.ThreeSum.LightDenseSetup.program_meets (d := d+1) (μ := μ)
    (a := av) (b := bv) (c := cv) (nA := A.length) (nB := B.length) (nC := C.length)
    (g := g) (recs := recs) (q := p) (aux := aux) (s := s) (cover := cover) (free := dst)
    (maxMod := _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n) (U := U) (h := _root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (J := J)
    (_root_.ThreeSum.LightPrimePool.prime (_root_.ThreeSum.Scales.primeWindow n)) rs hw (by omega) (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize_pos n)
    _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeReadyData.selected_pos hpmax (by omega) (by omega) (by omega)
    (by omega) haux hkey hspace hDenseWord H.cover H.normalized.2.2.2.2.2.1 hflags hvalid
    (fun i hi => by rw [hvalueA i hi]; exact hA i hi)
    (fun i hi => by rw [hvalueB i hi]; exact hB i hi)
    (fun i hi => by rw [hvalueC i hi]; exact hC i hi)
    hread (fun _ hi => (_root_.ThreeSum1960614.Machine.ThreeSum.LightPrimePool.prime_spec hi).1)
    (fun _ hi _ hj he => _root_.ThreeSum1960614.Machine.ThreeSum.LightPrimePool.prime_injective hi hj he) hproduct).append [_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumReportingSetupDense.body 19]
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     first
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hcall _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hcall ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, g, J, s]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [g, J, s] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, g, J, s] <;> omega)
     on_goal -1 => (rintro result ν ⟨hresult, hdense, _, hkeep⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have hscore : _root_.ThreeSum.LightDenseSetup.falseScore (_root_.ThreeSum.LightPrimePool.prime (_root_.ThreeSum.Scales.primeWindow n)) s p
      A.length B.length C.length g (fun i => μ (av+i)) (fun i => μ (bv+i)) (fun i => μ (cv+i)) rs=
      _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumColorBudgets.falseScore n A B C hsA hsB hsC := by
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumColorBudgets.falseScore
    rw [_root_.ThreeSum1960614.Machine.ThreeSum.LightDenseSetup.falseScore_eq,_root_.ThreeSum1960614.Machine.ThreeSum.LightDenseSetup.falseScore_eq]
    exact _root_.ThreeSum1960614.Machine.ThreeSum.BandWeightedScore.score_congr rs hvalueA hvalueB hvalueC
  rw [hscore] at hdense
  exact ⟨hresult,hdense,H.of_kept hkeep hprior,hkeep⟩
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightThreeSumReportingSetupDense.program_meets__implementation_2771687098) := (@ThreeSum1960614.Machine.ThreeSum.LightThreeSumReportingSetupDense.program_meets__implementation_2771687098)

#print axioms solution
