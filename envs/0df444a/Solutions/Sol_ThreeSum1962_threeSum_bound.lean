-- Prove2me | solution 1 for ThreeSum1962.threeSum_bound
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T19:30:05.693896+00:00
-- url     : https://prove2.me/submissions/3f70a726-6f0f-4799-b919-b13847216d81

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Aesop
import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Compiler_Cells
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Machine_Realized
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
import Definitions.Def_ThreeSum1962Source_Bundle18
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
import Mathlib.Algebra.Order.Floor.Semiring
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
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Normed.Field.Basic
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
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Function
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
import Mathlib.Order.Filter.AtTopBot.Basic
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
import Theorems.Thm_Light_Sec3_realized_threeSum
import Theorems.Thm_ThreeSumApsp_FromClaims_solvedAt_of_realized
import Theorems.Thm_ThreeSumApsp_WordRam_SolvedInTime_endStatement
import Theorems.Thm_ThreeSum_ArithmeticStageBounds_powerBound_of_fifth
import Theorems.Thm_ThreeSum_BandPrimeCosts_aggregate_time_le
import Theorems.Thm_ThreeSum_BandPrimeCosts_setup_time_le_budget
import Theorems.Thm_ThreeSum_BandPrimeCosts_timeBudget_powerBound
import Theorems.Thm_ThreeSum_BandScales_bandRoot_log_rate
import Theorems.Thm_ThreeSum_BandScales_bandSize_log_rate
import Theorems.Thm_ThreeSum_CostLedger_prefixBoxes_log_bound
import Theorems.Thm_ThreeSum_EncodedColorResources_dimensions
import Theorems.Thm_ThreeSum_HierarchyScales_bandCount_log_rate
import Theorems.Thm_ThreeSum_HierarchyScales_hierarchyEnvelope_log_rate
import Theorems.Thm_ThreeSum_HierarchyScales_initial_query_eventually_le
import Theorems.Thm_ThreeSum_LightLocalCoverCost_build_time_bound
import Theorems.Thm_ThreeSum_LightLocalCoverMagnitude_bounds
import Theorems.Thm_ThreeSum_LightOriginalOffset_time_bound
import Theorems.Thm_ThreeSum_LightRadixKeys_time_bound
import Theorems.Thm_ThreeSum_LightThreeSumHybrid_solves
import Theorems.Thm_ThreeSum_LocalParameterBounds_time_bound
import Theorems.Thm_ThreeSum_MassScales_falseNumerator_log_rate
import Theorems.Thm_ThreeSum_ModuloCosts_roundedPower_fifth
import Theorems.Thm_ThreeSum_ModuloCosts_time_bound
import Theorems.Thm_ThreeSum_Scales_natSqrt_ratio_tendsto_zero
import Theorems.Thm_ThreeSum_Scales_typedOutputs_log_ratio_tendsto
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_components
import Theorems.Thm_ThreeSum_SharedReportingCosts_overhead_powerBound
import Theorems.Thm_ThreeSum_StageBounds_PowerBound_add_same
import Theorems.Thm_ThreeSum_StageBounds_terminalChoices_log_rate
import Theorems.Thm_ThreeSum_SubsetAddress_enumerationWork_bound
import Theorems.Thm_ThreeSum_ThreeSumFastResourcesHybrid_poly_need
import Theorems.Thm_ThreeSum_TrimScales_fullOutputs_log_rate
import Theorems.Thm_ThreeSum_TrimScales_localLength_log_rate
import Theorems.Thm_ThreeSum_TrimScales_replicatedHalf_log_rate
import Theorems.Thm_ThreeSum_TrimScales_representationBound_log_rate
import Theorems.Thm_ThreeSum_UniformStageBounds_budget_active_powerBound


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace Light.Logs
end Light.Logs
namespace ThreeSum.ArithmeticStageBounds
end ThreeSum.ArithmeticStageBounds
namespace ThreeSum.BandCandidateRows
end ThreeSum.BandCandidateRows
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition
namespace ThreeSum.BandRawA
end ThreeSum.BandRawA
namespace ThreeSum.BandScales
end ThreeSum.BandScales
namespace ThreeSum.BlockEncoding
end ThreeSum.BlockEncoding
namespace ThreeSum.BlockIndexedQuery
end ThreeSum.BlockIndexedQuery
namespace ThreeSum.ColorClassLists
end ThreeSum.ColorClassLists
namespace ThreeSum.ColorParameters
end ThreeSum.ColorParameters
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
namespace ThreeSum.EncodedColorNormalizedData
end ThreeSum.EncodedColorNormalizedData
namespace ThreeSum.EncodedColorResources
end ThreeSum.EncodedColorResources
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.GlobalKeyEnumeration
end ThreeSum.GlobalKeyEnumeration
namespace ThreeSum.HierarchyScales
end ThreeSum.HierarchyScales
namespace ThreeSum.Karatsuba
end ThreeSum.Karatsuba
namespace ThreeSum.KaratsubaInterface
end ThreeSum.KaratsubaInterface
namespace ThreeSum.LightBlockQuery
end ThreeSum.LightBlockQuery
namespace ThreeSum.LightColorParametersCosts
end ThreeSum.LightColorParametersCosts
namespace ThreeSum.LightKaratsuba
end ThreeSum.LightKaratsuba
namespace ThreeSum.LightLocalCoverLayout
end ThreeSum.LightLocalCoverLayout
namespace ThreeSum.LightLocalCoverMagnitude
end ThreeSum.LightLocalCoverMagnitude
namespace ThreeSum.LightLocalCoverSchedule
end ThreeSum.LightLocalCoverSchedule
namespace ThreeSum.LightLocalCoverTables
end ThreeSum.LightLocalCoverTables
namespace ThreeSum.LightModuloCounts
end ThreeSum.LightModuloCounts
namespace ThreeSum.LightResidues
end ThreeSum.LightResidues
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.MassScales
end ThreeSum.MassScales
namespace ThreeSum.ModuloCosts
end ThreeSum.ModuloCosts
namespace ThreeSum.Parameters
end ThreeSum.Parameters
namespace ThreeSum.RawAKeyLists
end ThreeSum.RawAKeyLists
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.RawReporting
end ThreeSum.RawReporting
namespace ThreeSum.ReportingHostFrontierLayout
end ThreeSum.ReportingHostFrontierLayout
namespace ThreeSum.ReportingHostLevelData
end ThreeSum.ReportingHostLevelData
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.SharedReportingCosts
end ThreeSum.SharedReportingCosts
namespace ThreeSum.StageBounds
end ThreeSum.StageBounds
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum.Switch
end ThreeSum.Switch
namespace ThreeSum.TrimScales
end ThreeSum.TrimScales
namespace ThreeSum.UniformStageBounds
end ThreeSum.UniformStageBounds
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec

section


/-!
# Logarithms, the cube root and halves, without division

Four routines on local variables only; none of them touches the memory.

* log2(x) returns ⌊log₂ x⌋ (0 for x = 0) by doubling (`log2_meets`).
* clog2(x) returns ⌈log₂ x⌉ (0 for x ≤ 1) by doubling (`clog2_meets`).
* cbrtCeil(n) returns the least s with s³ ≥ n, which is ⌈n^{1/3}⌉, by counting up
  (`cbrtCeil_meets`).
* half(h) returns ⌈h/2⌉ by counting up (`half_meets`).

Each of them is one loop that tries the candidates 0, 1, 2, … in turn.  Local variable 0 holds the
argument and receives the result, local variable 1 holds the candidate (`Arg`, `Cand`), and the two
logarithms keep a power of two in local variable 2 (`Power`).
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

namespace Logs







end Logs

open Logs

/-! ## The logarithm, rounded down -/















































/-! ## The logarithm, rounded up -/










































/-! ## The cube root, rounded up -/












theorem cbrtLeast_le {n s : ℕ} (h : n ≤ s ^ 3) : cbrtLeast n ≤ s :=
  Nat.find_min' (exists_le_cube n) h

theorem cbrtLeast_le_self (n : ℕ) : cbrtLeast n ≤ n :=
  cbrtLeast_le (Nat.le_self_pow (by norm_num) n)


















































































/-! ## Halves, rounded up -/

































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























































theorem time_bound (k : ℕ) : time k + 2500 * 2 ^ k ≤ 2530 * 3 ^ k := by
  induction k with
  | zero => norm_num [time]
  | succ k ih =>
    simp only [time, pow_succ]
    nlinarith

theorem time_le (k : ℕ) : time k ≤ 2530 * 3 ^ k :=
  (Nat.le_add_right _ _).trans (time_bound k)

























































section Join

variable {lim : Limits} {P : Program} {d pLinear pFill : ℕ}




































































































































end Join

section BaseCase

variable {lim : Limits} {P : Program} {d : ℕ}






































end BaseCase

















































































































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
# Uniform bounds for repeated modular-counting calls

A caller may reserve resources for the largest modulus it will use. These
lemmas relate that reservation to the exact costed program contract.
-/

namespace ThreeSum.ModuloRuntime

open LightModuloCounts KaratsubaInterface

theorem capacity_mono {p q : ℕ} (h : p ≤ q) : capacity p ≤ capacity q := by
  exact Nat.pow_le_pow_right (by decide) (Nat.clog_mono_right 2 h)

theorem karatsuba_time_mono : Monotone LightKaratsuba.time := by
  apply monotone_nat_of_le_succ
  intro k
  rw [LightKaratsuba.time]
  omega

theorem time_mono {p q : ℕ} (h : p ≤ q) (nA nB nC U : ℕ) :
    time p nA nB nC U ≤ time q nA nB nC U := by
  have hc := capacity_mono h
  have hl := Nat.clog_mono_right 2 h
  have ht := karatsuba_time_mono hl
  unfold time LightCapacity.time LightResidueHistogram.time
    LightHistogram.histogramTime LightCyclic.combinedTime
  simp only [Light.fillTime, LightArray.linearTime]
  omega
















































end ThreeSum.ModuloRuntime

end

section


/-!
# Finite arithmetic-operation bounds for the complete counting backend

The only input-size dependence outside the Karatsuba term is the number of
original elements times their remainder bit budget. Histogram initialization,
capacity computation and folding are included in the displayed constant.
-/

namespace ThreeSum.ModuloCosts

open KaratsubaInterface



theorem capacity_le_roundedPower (p : ℕ) : capacity p ≤ roundedPower p :=
  Nat.pow_le_pow_left (by decide) _

theorem log_le_roundedPower (p : ℕ) : Nat.clog 2 p ≤ roundedPower p :=
  (Nat.lt_pow_self (by decide : 1 < 2)).le.trans (capacity_le_roundedPower p)







































end ThreeSum.ModuloCosts

end

section


/-!
# Analytic and rational parameter certificate for the proposed 3SUM algorithm

This module certifies the real-variable inequalities and the resulting exponent ledger.
It does not by itself prove that an implementation has those costs: the reduction,
cover, encoding, reporting, arithmetic and machine-model lemmas are separate obligations.

All decimal-looking constants below are exact rational numbers. There are no numerical
oracles, admitted declarations, or native-code decision procedures in this certificate.
-/

noncomputable section

namespace ThreeSum.Parameters

open Set Real

set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048







































/-! ## Exact integer witnesses for the logarithmic comparisons -/








theorem power_initial_entropy : (25 : ℕ) ^ 100 < 2 ^ 25 * 24 ^ 96 := by norm_num




























private theorem log_512 : Real.log 512 = 9 * Real.log 2 := by
  have h := Real.log_pow (2 : ℝ) 9
  norm_num at h
  exact h























/-- A one-term atanh estimate, proved by Mathlib's uniform remainder theorem. -/
theorem log_ratio_upper_one {x : ℝ} (hx : |x| < 1) :
    Real.log ((1 + x) / (1 - x)) ≤ 2 * x + 2 * |x| ^ 3 / (1 - x ^ 2) := by
  have h := (abs_le.mp (Real.sum_range_sub_log_div_le hx 1)).2
  norm_num [Finset.sum_range_succ] at h
  rw [show 2 * |x| ^ 3 / (1 - x ^ 2) = 2 * (|x| ^ 3 / (1 - x ^ 2)) by ring]
  linarith

theorem kappa_formula :
    kappa * Real.log 2 =
      256 * Real.log (512 / 511) + 255 * Real.log (510 / 511) := by
  have h510 : Real.log (510 : ℝ) = Real.log 2 + Real.log 255 := by
    rw [show (510 : ℝ) = 2 * 255 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  norm_num [kappa, entropy, Real.binEntropy]
  rw [Real.log_div (by norm_num : (512 : ℝ) ≠ 0) (by norm_num : (511 : ℝ) ≠ 0),
    Real.log_div (by norm_num : (256 : ℝ) ≠ 0) (by norm_num : (255 : ℝ) ≠ 0),
    Real.log_div (by norm_num : (510 : ℝ) ≠ 0) (by norm_num : (511 : ℝ) ≠ 0),
    log_256, log_512, h510]
  field_simp
  ring

theorem kappa_bound : kappa < kappaCap := by
  have hp := log_ratio_upper_one (x := (1 / 1023 : ℝ)) (by norm_num)
  have hm := log_ratio_upper_one (x := -(1 / 1021 : ℝ)) (by norm_num)
  norm_num at hp hm
  have hnum : kappa * Real.log 2 ≤ (1 / 1021 : ℝ) := by
    rw [kappa_formula]
    linarith
  have hsmall : kappa * Real.log 2 < (3 / 2000) * Real.log 2 := by
    linarith [log_two_lower]
  exact (mul_lt_mul_iff_of_pos_right log_two_pos).mp hsmall



















































theorem initial_entropy_bound : entropy initialTheta < (1 / 4 : ℝ) := by
  have hp : (25 : ℝ) ^ 100 < 2 ^ 25 * 24 ^ 96 := by
    exact_mod_cast power_initial_entropy
  have h := Real.log_lt_log (by positivity : (0 : ℝ) < 25 ^ 100) hp
  rw [Real.log_mul (by positivity : (2 : ℝ) ^ 25 ≠ 0)
    (by positivity : (24 : ℝ) ^ 96 ≠ 0)] at h
  simp only [Real.log_pow] at h
  norm_num at h
  norm_num [initialTheta, entropy, Real.binEntropy]
  rw [Real.log_div (by norm_num : (25 : ℝ) ≠ 0) (by norm_num : (24 : ℝ) ≠ 0),
    div_lt_iff₀ log_two_pos]
  linarith

/-! ## Exact rational inequalities for the schedule -/














































































































































































































































































theorem certificate_lt_target : certificateExponent < targetExponent := by
  norm_num [certificateExponent, targetExponent]

/-! ## The real-valued ledger, before the algorithmic cost lemmas are applied -/
















/-- Uniform ledger bounds; the hypotheses must be supplied by the analytic certificate. -/
theorem cost_ledger_bounds {e k h : ℝ} (he0 : 4 < e) (he1 : e < 19 / 4)
    (hk : k < kappaCap) (hh : h < 1 / 4) :
    2 * epsilon * e < 19 / 10 ∧
    1 + epsilon * (e - bandShift) < 49 / 25 ∧
    2 - epsilon * boxSaving = 9809 / 5000 ∧
    2 - epsilon * (1 / 2 + bandShift - h) < 49 / 25 ∧
    2 - epsilon * (1 / 2 - bandShift - k - entropyRatio * (1 + boxSaving - 2 * bandShift))
      < certificateExponent ∧
    2 - epsilon * (terminalFraction - 1 / 2 - bandShift - k) < 19603 / 10000 ∧
    epsilon * (8 / 5) * (e + 1 / 2) < 42 / 25 ∧
    2 + epsilon * (4 / 5 - (2 / 5) * e - 2 * bandShift) < 93 / 50 ∧
    1 + epsilon * (1 / 2 - bandShift) = 111 / 100 ∧
    2 - epsilon * (e + bandShift) < 121 / 100 ∧
    2 - 2 * epsilon * (e + bandShift) < 21 / 50 ∧
    epsilon * (e + bandShift) < 1 := by
  dsimp [epsilon, bandShift, boxSaving, entropyRatio, terminalFraction,
    certificateExponent, kappaCap] at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith










/-- The ledger instantiated with the entropy-defined parameters, with no analytic hypotheses. -/
theorem all_costs_le_certificate :
    ∀ t ∈ costLedger E kappa (entropy initialTheta), t ≤ certificateExponent := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ :=
    cost_ledger_bounds E_bounds.1 E_bounds.2 kappa_bound initial_entropy_bound
  intro t ht
  simp only [costLedger, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    dsimp [certificateExponent] at * <;> linarith







end ThreeSum.Parameters

end
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

















































































































theorem muZero_square_log_ratio_tendsto_zero :
    Tendsto (fun n : ℕ => (muZero n : ℝ) ^ 2 / Real.log n) atTop (𝓝 0) := by
  have h := (microSize_square_ratio_tendsto_zero.comp inputBits_tendsto_atTop).mul
    inputBits_log_ratio_tendsto
  simp only [zero_mul] at h
  apply h.congr'
  filter_upwards [inputBits_tendsto_atTop.eventually (eventually_ge_atTop 1)] with n hn
  have hn0 : (inputBits n : ℝ) ≠ 0 := by exact_mod_cast (by omega : inputBits n ≠ 0)
  simp only [Function.comp_def, muZero]
  field_simp


























































theorem localSearch_log_ratio_tendsto_zero (C : ℕ) :
    Tendsto (fun n : ℕ => Real.log (localSearch C n : ℝ) / Real.log n) atTop (𝓝 0) := by
  have h := muZero_square_log_ratio_tendsto_zero.const_mul ((C : ℝ) * Real.log 2)
  simpa [localSearch, Nat.cast_pow, Nat.cast_mul, Real.log_pow, mul_div_assoc,
    mul_comm, mul_left_comm, mul_assoc] using h

















/-- Converts a proved logarithmic rate into a power bound; the concrete
table and construction functions are instantiated immediately below. -/
theorem eventually_le_rpow_of_log_ratio {f : ℕ → ℕ} {a d : ℝ}
    (hf : Tendsto (fun n : ℕ => Real.log (f n : ℝ) / Real.log n) atTop (𝓝 a))
    (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, (f n : ℝ) ≤ (n : ℝ) ^ (a + d) := by
  have hs := hf.eventually (gt_mem_nhds (by linarith : a < a + d))
  filter_upwards [hs, eventually_ge_atTop (2 : ℕ)] with n hn hge
  have hnp : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hlog : 0 < Real.log n := Real.log_pos hnp
  exact Real.le_rpow_of_log_le (by linarith) ((div_lt_iff₀ hlog).mp hn).le

theorem localSearch_subpolynomial (C : ℕ) {d : ℝ} (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, (localSearch C n : ℝ) ≤ (n : ℝ) ^ d := by
  simpa using eventually_le_rpow_of_log_ratio (localSearch_log_ratio_tendsto_zero C) hd































theorem windowExponent_ratio_tendsto_zero :
    Tendsto (fun m : ℕ => (windowExponent m : ℝ) / m) atTop (𝓝 0) := by
  have h := natSqrt_ratio_tendsto_zero.add
    (tendsto_natCast_atTop_atTop (R := ℝ)).inv_tendsto_atTop
  simpa [windowExponent, Nat.cast_add, add_div, one_div] using h

















theorem primeWindow_log_ratio_tendsto_zero :
    Tendsto (fun n : ℕ => Real.log (primeWindow n : ℝ) / Real.log n) atTop (𝓝 0) := by
  have h := ((windowExponent_ratio_tendsto_zero.comp inputBits_tendsto_atTop).mul
    inputBits_log_ratio_tendsto).const_mul (Real.log 2)
  simp only [zero_mul, mul_zero] at h
  apply h.congr'
  filter_upwards [inputBits_tendsto_atTop.eventually (eventually_ge_atTop 1)] with n hn
  have hn0 : (inputBits n : ℝ) ≠ 0 := by exact_mod_cast (by omega : inputBits n ≠ 0)
  simp only [Function.comp_def, primeWindow, Nat.cast_pow, Real.log_pow, Nat.cast_ofNat]
  field_simp






















































theorem muZero_eq_twice_half (n : ℕ) : muZero n = 2 * microHalf (inputBits n) := rfl











































































































































































































































































































































































































































































































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


































theorem scheduleCount_log_rate :
    Tendsto (fun n : ℕ => Real.log (scheduleCount n : ℝ) / Real.log n) atTop (𝓝 0) := by
  simpa [scheduleCount] using replicatedHalf_log_rate localLength_log_rate
























theorem mu_cast_tendsto_atTop : Tendsto (fun n : ℕ => (mu n : ℝ)) atTop atTop := by
  have hpos : (0 : ℝ) < 1 / (5 * Real.log 2) := by positivity
  have h := mu_log_ratio_tendsto.pos_mul_atTop hpos Asymptotics.log_nat_tendsto_atTop
  apply h.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
  have hlog : Real.log n ≠ 0 := (Real.log_pos (by exact_mod_cast (by omega : 1 < n))).ne'
  exact div_mul_cancel₀ _ hlog

theorem mu_tendsto_atTop : Tendsto mu atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [mu_cast_tendsto_atTop.eventually (eventually_ge_atTop (b : ℝ))] with n hn
  exact_mod_cast hn
































































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







theorem mu_multiple_twenty (n : ℕ) : 20 ∣ mu n := by
  unfold mu totalSize blockCount
  exact ⟨(inputBits n / (100 * microSize (inputBits n))) * microSize (inputBits n), by ring⟩

theorem typedOutputs_pos (n : ℕ) : 0 < typedOutputs n := by
  unfold typedOutputs
  exact Nat.pow_pos (Nat.choose_pos (by omega))



























noncomputable section















































theorem mu_div_twenty_real (n : ℕ) : (mu n / 20 : ℕ) = (mu n : ℝ) / 20 := by
  have h := Nat.div_mul_cancel (mu_multiple_twenty n)
  have hr : ((mu n / 20 : ℕ) : ℝ) * 20 = mu n := by exact_mod_cast h
  linarith

theorem bandDivisor_log_rate :
    Tendsto (fun n : ℕ => Real.log (bandDivisor n : ℝ) / Real.log n) atTop (𝓝 (1 / 100)) := by
  have h := mu_log_ratio_tendsto.const_mul (Real.log 2 / 20)
  have heq : (Real.log 2 / 20) * (1 / (5 * Real.log 2)) = (1 / 100 : ℝ) := by field_simp; norm_num
  rw [heq] at h
  convert h using 1
  funext n
  simp only [bandDivisor, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow, mu_div_twenty_real]
  ring




































































end

end ThreeSum.BandScales

end

section


/-!
# The executable integer cubic switch

The implementation scans integers `q ≤ r/2` and tests a cleared integer
inequality.  No real-number comparison, logarithm oracle, or unbounded
noncomputable search occurs in the definition.  For admissible depths the
candidate set is nonempty.  Minimality gives the exact `9/r` rounding error
needed by the certified box and entropy bounds.
-/

namespace ThreeSum.Switch

open Set ThreeSum.Parameters ThreeSum.Scales

set_option maxHeartbeats 0





































noncomputable section



































































































































theorem actual_totalSize (n : ℕ) : mu n = blockCount (inputBits n) * muZero n := rfl




theorem actual_depth_condition {n j : ℕ} (hj : j ≤ terminalDepth n) :
    20 * j ≤ 13 * blockCount (inputBits n) := by
  have hm := Nat.div_mul_le_self (13 * blockCount (inputBits n)) 20
  unfold terminalDepth at hj
  omega




























































end
end ThreeSum.Switch

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
# Finite sums and asymptotic bounds for the actual hierarchy

The finite box and query counts are summed over the executable depth range.
The only envelopes introduced here are explicit elementary functions of the
already constructed integer `mu`; all growth rates are proved from Scales.
-/

namespace ThreeSum.HierarchyScales

open Filter Set Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.Switch ThreeSum.CostLedger
open scoped Topology BigOperators

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
































theorem terminalDepth_le_mu {n : ℕ} (hmu : 0 < mu n) : terminalDepth n ≤ mu n := by
  have hprod := hmu
  rw [actual_totalSize] at hprod
  have hm := Nat.pos_of_mul_pos_left hprod
  have hc := Nat.mul_le_mul_left (blockCount (inputBits n)) (show 1 ≤ muZero n by omega)
  have hd := actual_depth_condition (n := n) (j := terminalDepth n) le_rfl
  rw [Nat.mul_one, ← actual_totalSize] at hc
  omega

noncomputable section




theorem allPrefixBoxes_envelope {n : ℕ} (hmu : 0 < mu n) :
    (allPrefixBoxes n : ℝ) ≤ hierarchyEnvelope (2 * E + 2 * bandShift - boxSaving) 0 n := by
  unfold allPrefixBoxes
  rw [Nat.cast_sum]
  calc
    _ ≤ ∑ j ∈ Finset.range (terminalDepth n + 1),
        Real.exp ((mu n : ℝ) * Real.log 2 * (2 * E + 2 * bandShift - boxSaving)) := by
      apply Finset.sum_le_sum
      intro j hj
      exact Real.le_exp_of_log_le (prefixBoxes_log_bound hmu (by simpa using hj))
    _ = (terminalDepth n + 1 : ℝ) *
        Real.exp ((mu n : ℝ) * Real.log 2 * (2 * E + 2 * bandShift - boxSaving)) := by simp
    _ ≤ hierarchyEnvelope (2 * E + 2 * bandShift - boxSaving) 0 n := by
      simp only [hierarchyEnvelope, add_zero]
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      exact_mod_cast Nat.add_le_add_right (terminalDepth_le_mu hmu) 1

















































theorem eventually_real_le_rpow_of_log_rate {f : ℕ → ℝ} {a d : ℝ}
    (hf : Tendsto (fun n : ℕ => Real.log (f n) / Real.log n) atTop (𝓝 a)) (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, f n ≤ (n : ℝ) ^ (a + d) := by
  have hs := hf.eventually (gt_mem_nhds (by linarith : a < a + d))
  filter_upwards [hs, eventually_ge_atTop (2 : ℕ)] with n hn hge
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  exact Real.le_rpow_of_log_le (by exact_mod_cast (by omega : 0 < n))
    ((div_lt_iff₀ hlog).mp hn).le

theorem allPrefixBoxes_eventually_le {d : ℝ} (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, (allPrefixBoxes n : ℝ) ≤
      (n : ℝ) ^ ((2 * E + 2 * bandShift - boxSaving) / 5 + d) := by
  have he := eventually_real_le_rpow_of_log_rate
    (hierarchyEnvelope_log_rate (2 * E + 2 * bandShift - boxSaving) 0) hd
  filter_upwards [he, TrimScales.mu_tendsto_atTop.eventually (eventually_ge_atTop 1)] with n hn hmu
  exact (allPrefixBoxes_envelope (by omega : 0 < mu n)).trans hn



























































































































































































end
end ThreeSum.HierarchyScales

end

section


/-!
# Actual wanted-incidence and false-mass majorants

The numerator of the wanted bound retains all raw A occurrences, all three
arithmetic lifts, and every schedule occurrence.  The false bound uses the
actual candidate count, integer band count, score loss, and modulus loss.
No asymptotic premise about an input-dependent mass is assumed here: the
transfer lemmas take the explicit finite inequalities from the counting
and prime-chain algorithms.
-/

namespace ThreeSum.MassScales

open Filter Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.TrimScales
  ThreeSum.BandScales ThreeSum.CostLedger ThreeSum.HierarchyScales
open scoped Topology

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000









theorem scheduleCount_pos (n : ℕ) : 0 < scheduleCount n :=
  Nat.pow_pos (localLength_pos _)

theorem bandCount_pos {n : ℕ} (hn : 0 < n) : 0 < bandCount n :=
  Nat.pos_of_mul_pos_left (hn.trans_le (bandCount_mul_bounds n).1)

theorem rawTripleBound_pos {n : ℕ} (hn : 0 < n) : 0 < rawTripleBound n := by
  have hB := bandCount_pos hn
  have hb := bandSize_pos n
  unfold rawTripleBound
  positivity

theorem wantedNumerator_pos {n : ℕ} (hn : 0 < n) : 0 < wantedNumerator n := by
  have hS := scheduleCount_pos n
  have hM := typedOutputs_pos n
  have hB := bandCount_pos hn
  have hb := bandSize_pos n
  exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by norm_num) hS) hM)
    (Nat.pow_pos hB)) hb

theorem scoreLoss_pos (k n : ℕ) : 0 < scoreLoss k n := by
  unfold scoreLoss
  positivity

theorem primeLoss_pos (n : ℕ) : 0 < primeLoss radix n := by
  have hy := primeWindow_ge_two n
  unfold primeLoss
  positivity

theorem candidateCount_eventually_pos : ∀ᶠ n : ℕ in atTop, 0 < candidateCount n := by
  filter_upwards [actual_candidates_nonempty] with n hn
  exact Finset.card_pos.mpr hn

theorem falseNumerator_eventually_pos (k : ℕ) :
    ∀ᶠ n : ℕ in atTop, 0 < falseNumerator k n := by
  filter_upwards [candidateCount_eventually_pos, eventually_ge_atTop (1 : ℕ)] with n hC hn
  have ht := rawTripleBound_pos (by omega : 0 < n)
  have hs := scoreLoss_pos k n
  have hp := primeLoss_pos n
  unfold falseNumerator
  positivity

noncomputable section





theorem nat_log_rate_const (c : ℕ) :
    Tendsto (fun n : ℕ => Real.log (c : ℝ) / Real.log n) atTop (𝓝 0) := by
  simpa only [mul_zero, Pi.inv_apply, div_eq_mul_inv] using
    Asymptotics.log_nat_tendsto_atTop.inv_tendsto_atTop.const_mul (Real.log (c : ℝ))

theorem nat_log_rate_mul {f g : ℕ → ℕ} {a b : ℝ}
    (hf : Tendsto (fun n : ℕ => Real.log (f n : ℝ) / Real.log n) atTop (𝓝 a))
    (hg : Tendsto (fun n : ℕ => Real.log (g n : ℝ) / Real.log n) atTop (𝓝 b))
    (hp : ∀ᶠ n : ℕ in atTop, 0 < f n ∧ 0 < g n) :
    Tendsto (fun n : ℕ => Real.log ((f n * g n : ℕ) : ℝ) / Real.log n) atTop (𝓝 (a + b)) := by
  apply (hf.add hg).congr'
  filter_upwards [hp] with n hn
  have hfR : (f n : ℝ) ≠ 0 := by exact_mod_cast hn.1.ne'
  have hgR : (g n : ℝ) ≠ 0 := by exact_mod_cast hn.2.ne'
  simp only [Nat.cast_mul, Real.log_mul hfR hgR, add_div]

theorem nat_log_rate_pow {f : ℕ → ℕ} {a : ℝ}
    (hf : Tendsto (fun n : ℕ => Real.log (f n : ℝ) / Real.log n) atTop (𝓝 a)) (k : ℕ) :
    Tendsto (fun n : ℕ => Real.log ((f n ^ k : ℕ) : ℝ) / Real.log n) atTop (𝓝 ((k : ℝ) * a)) := by
  simpa only [Nat.cast_pow, Real.log_pow, mul_div_assoc] using hf.const_mul (k : ℝ)

























theorem bandSize_log_rate_shift :
    Tendsto (fun n : ℕ => Real.log (bandSize n : ℝ) / Real.log n) atTop
      (𝓝 ((E + bandShift) / 5)) := by
  simpa only [bandShift, sub_eq_add_neg] using BandScales.bandSize_log_rate

theorem wantedNumerator_log_rate :
    Tendsto (fun n : ℕ => Real.log (wantedNumerator n : ℝ) / Real.log n) atTop
      (𝓝 (2 + 2 * E / 5 - (E + bandShift) / 5)) := by
  have h1 := nat_log_rate_mul (nat_log_rate_const 9) scheduleCount_log_rate (by
    filter_upwards [] with n
    exact ⟨by norm_num, scheduleCount_pos n⟩)
  have h2 := nat_log_rate_mul h1 typedOutputs_log_ratio_tendsto (by
    filter_upwards [] with n
    exact ⟨Nat.mul_pos (by norm_num) (scheduleCount_pos n), typedOutputs_pos n⟩)
  have h3 := nat_log_rate_mul h2 (nat_log_rate_pow bandCount_log_rate 2) (by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    exact ⟨Nat.mul_pos (Nat.mul_pos (by norm_num) (scheduleCount_pos n)) (typedOutputs_pos n),
      Nat.pow_pos (bandCount_pos (by omega))⟩)
  have h4 := nat_log_rate_mul h3 bandSize_log_rate_shift (by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    refine ⟨?_, bandSize_pos n⟩
    exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by norm_num) (scheduleCount_pos n))
      (typedOutputs_pos n)) (Nat.pow_pos (bandCount_pos (by omega))))
  convert h4 using 1 <;> simp only [wantedNumerator, Nat.cast_ofNat] <;> ring




























theorem wantedMajorant_log_rate :
    Tendsto (fun n : ℕ => Real.log (wantedMajorant n) / Real.log n) atTop
      (𝓝 (2 - (1 / 2 + bandShift) / 5)) := by
  have hh := wantedNumerator_log_rate.sub radix_log_ratio_tendsto
  have hid : (2 + 2 * E / 5 - (E + bandShift) / 5) - (E + 1 / 2) / 5 =
      2 - (1 / 2 + bandShift) / 5 := by ring
  rw [hid] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hN : (wantedNumerator n : ℝ) ≠ 0 := by exact_mod_cast (wantedNumerator_pos (by omega : 0 < n)).ne'
  have hR : (radix n : ℝ) ≠ 0 := by exact_mod_cast (radix_pos n).ne'
  simp only [wantedMajorant, Real.log_div hN hR, sub_div]

theorem falseMajorant_log_rate (k : ℕ) :
    Tendsto (fun n : ℕ => Real.log (falseMajorant k n) / Real.log n) atTop
      (𝓝 (2 - (1 / 2 - bandShift) / 5)) := by
  have hh := (falseNumerator_log_rate k).sub radix_log_ratio_tendsto
  have hid : (2 + (E + bandShift) / 5) - (E + 1 / 2) / 5 =
      2 - (1 / 2 - bandShift) / 5 := by ring
  rw [hid] at hh
  apply hh.congr'
  filter_upwards [falseNumerator_eventually_pos k] with n hn
  have hN : (falseNumerator k n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hR : (radix n : ℝ) ≠ 0 := by exact_mod_cast (radix_pos n).ne'
  simp only [falseMajorant, Real.log_div hN hR, sub_div]

theorem wantedMajorant_eventually_le {d : ℝ} (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, wantedMajorant n ≤ (n : ℝ) ^ (2 - (1 / 2 + bandShift) / 5 + d) :=
  eventually_real_le_rpow_of_log_rate wantedMajorant_log_rate hd

theorem falseMajorant_eventually_le (k : ℕ) {d : ℝ} (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, falseMajorant k n ≤ (n : ℝ) ^ (2 - (1 / 2 - bandShift) / 5 + d) :=
  eventually_real_le_rpow_of_log_rate (falseMajorant_log_rate k) hd

theorem wanted_mass_le {n W : ℕ} (hW : W * radix n ≤ wantedNumerator n) :
    (W : ℝ) ≤ wantedMajorant n := by
  rw [wantedMajorant, le_div_iff₀ (show (0 : ℝ) < radix n by exact_mod_cast radix_pos n)]
  exact_mod_cast hW

















end
end ThreeSum.MassScales

end

section


/-!
# The six principal finite stage counts

This module assembles actual natural-number work quantities.  Its final
theorem is a runtime-ledger target, not a 3SUM correctness or machine-time
theorem.  The only input-dependent assumptions are four explicit finite
counting inequalities for the wanted mass and the prime-chain score.
An implementation must still connect its operation counter to these counts.
-/

namespace ThreeSum.StageBounds

open Filter Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.TrimScales
  ThreeSum.BandScales ThreeSum.Switch ThreeSum.CostLedger ThreeSum.HierarchyScales
  ThreeSum.MassScales
open scoped Topology

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000


























noncomputable section





namespace PowerBound

theorem of_rate {f : ℕ → ℕ} {a : ℝ}
    (hf : Tendsto (fun n : ℕ => Real.log (f n : ℝ) / Real.log n) atTop (𝓝 a)) : PowerBound f a :=
  fun _ hd => eventually_le_rpow_of_log_ratio hf hd

theorem const (c : ℕ) : PowerBound (fun _ => c) 0 := of_rate (nat_log_rate_const c)

theorem mul {f g : ℕ → ℕ} {a b : ℝ} (hf : PowerBound f a) (hg : PowerBound g b) :
    PowerBound (fun n => f n * g n) (a + b) := by
  intro d hd
  filter_upwards [hf (d / 2) (by linarith), hg (d / 2) (by linarith),
    eventually_ge_atTop (1 : ℕ)] with n hfn hgn hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  rw [Nat.cast_mul]
  calc
    _ ≤ (n : ℝ) ^ (a + d / 2) * (n : ℝ) ^ (b + d / 2) :=
      mul_le_mul hfn hgn (Nat.cast_nonneg _) (Real.rpow_nonneg hnR.le _)
    _ = (n : ℝ) ^ ((a + b) + d) := by rw [← Real.rpow_add hnR]; congr 1; ring

theorem mono_exponent {f : ℕ → ℕ} {a b : ℝ} (hf : PowerBound f a) (hab : a ≤ b) :
    PowerBound f b := by
  intro d hd
  filter_upwards [hf d hd, eventually_ge_atTop (1 : ℕ)] with n hn hge
  exact hn.trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hge) (by linarith))















theorem pow {f : ℕ → ℕ} {a : ℝ} (hf : PowerBound f a) (k : ℕ) :
    PowerBound (fun n => f n ^ k) ((k : ℝ) * a) := by
  induction k with
  | zero => simpa only [Nat.cast_zero, zero_mul, pow_zero] using const 1
  | succ k ih =>
      simpa only [Nat.pow_succ, Nat.cast_add, Nat.cast_one, add_mul, one_mul] using ih.mul hf

end PowerBound

theorem wanted_powerBound {W : ℕ → ℕ}
    (hW : ∀ᶠ n : ℕ in atTop, W n * radix n ≤ wantedNumerator n) :
    PowerBound W (2 - (1 / 2 + bandShift) / 5) := by
  intro d hd
  filter_upwards [hW, wantedMajorant_eventually_le hd] with n hn he
  exact (wanted_mass_le hn).trans he

















theorem encoder_powerBound : PowerBound encoderCount (1 + epsilon * (E - bandShift)) := by
  have hh := (((PowerBound.const 2).mul (PowerBound.of_rate bandCount_log_rate)).mul
    (PowerBound.of_rate scheduleCount_log_rate)).mul (PowerBound.of_rate fullOutputs_log_rate)
  have heq : ((0 : ℝ) + (1 - (E + bandShift) / 5) + 0) + 2 * E / 5 =
      1 + epsilon * (E - bandShift) := by unfold epsilon; ring
  rw [heq] at hh
  exact hh

theorem boxes_powerBound : PowerBound boxCount (2 - epsilon * boxSaving) := by
  have hB := PowerBound.of_rate (nat_log_rate_pow bandCount_log_rate 2)
  have hQ : PowerBound allPrefixBoxes ((2 * E + 2 * bandShift - boxSaving) / 5) :=
    fun _ hd => allPrefixBoxes_eventually_le hd
  have hh := (((PowerBound.const 3).mul hB).mul (PowerBound.of_rate scheduleCount_log_rate)).mul hQ
  have heq : ((0 : ℝ) + 2 * (1 - (E + bandShift) / 5) + 0) +
      (2 * E + 2 * bandShift - boxSaving) / 5 = 2 - epsilon * boxSaving := by unfold epsilon; ring
  norm_num only [Nat.cast_ofNat] at hh
  rw [heq] at hh
  exact hh

theorem initial_powerBound {W : ℕ → ℕ}
    (hW : ∀ᶠ n : ℕ in atTop, W n * radix n ≤ wantedNumerator n) :
    PowerBound (initialCount W) (2 - epsilon * (1 / 2 + bandShift - entropy initialTheta)) := by
  have hQ : PowerBound (fun n => queryTerms n 0) (entropy initialTheta / 5) :=
    fun _ hd => initial_query_eventually_le hd
  have hh := (wanted_powerBound hW).mul hQ
  have heq : (2 - (1 / 2 + bandShift) / 5) + entropy initialTheta / 5 =
      2 - epsilon * (1 / 2 + bandShift - entropy initialTheta) := by unfold epsilon; ring
  rw [heq] at hh
  exact hh





















































































































end
end ThreeSum.StageBounds

end

section


/-!
# A uniform size-only budget for the six principal stage counts

Both mass budgets are executable integer divisions of the concrete size
majorants.  The final bound is uniform in the input-dependent masses: the
eventual size threshold is chosen before `W`, `H`, `P`, or `H1` are quantified.
This remains a theorem about the specified finite work quantities, not a
claim that a complete machine has been proved to execute within them.
-/

namespace ThreeSum.UniformStageBounds

open Filter Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.TrimScales
  ThreeSum.BandScales ThreeSum.Switch ThreeSum.CostLedger ThreeSum.HierarchyScales
  ThreeSum.MassScales ThreeSum.StageBounds
open scoped Topology

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000










theorem wantedBudget_mul_le (n : ℕ) : wantedBudget n * radix n ≤ wantedNumerator n :=
  Nat.div_mul_le_self _ _

noncomputable section










theorem wantedBudget_powerBound : PowerBound wantedBudget (2 - (1 / 2 + bandShift) / 5) :=
  wanted_powerBound (Filter.Eventually.of_forall wantedBudget_mul_le)

theorem falseBudget_powerBound (k : ℕ) : PowerBound (falseBudget k) (2 - (1 / 2 - bandShift) / 5) := by
  intro d hd
  filter_upwards [falseMajorant_eventually_le k hd] with n hn
  have hb : (falseBudget k n : ℝ) ≤ falseMajorant k n := by
    rw [falseMajorant, le_div_iff₀ (show (0 : ℝ) < radix n by exact_mod_cast radix_pos n)]
    exact_mod_cast Nat.div_mul_le_self (falseNumerator k n) (radix n)
  exact hb.trans hn

theorem budget_initial_powerBound :
    PowerBound (initialCount wantedBudget)
      (2 - epsilon * (1 / 2 + bandShift - entropy initialTheta)) :=
  initial_powerBound (Filter.Eventually.of_forall wantedBudget_mul_le)



















theorem budget_terminal_powerBound (k : ℕ) :
    PowerBound (terminalCount (falseBudget k))
      (2 - epsilon * (terminalFraction - 1 / 2 - bandShift - kappa)) := by
  have hh := (((PowerBound.const 2).mul (falseBudget_powerBound k)).mul
    (PowerBound.of_rate representationBound_log_rate)).mul (PowerBound.of_rate terminalChoices_log_rate)
  have heq : ((0 : ℝ) + (2 - (1 / 2 - bandShift) / 5) + kappa / 5) +
      (1 - terminalFraction) / 5 =
      2 - epsilon * (terminalFraction - 1 / 2 - bandShift - kappa) := by unfold epsilon; ring
  rw [heq] at hh
  exact hh








































































end
end ThreeSum.UniformStageBounds

end

section


/-!
# The arithmetic and balancing work outside the six reporting stages

The finite bounds here include complete modular-counting invocations, their
signed-remainder bit cost, and the actual correlation/minimum routine. They
augment the six-stage reporting budget. The whole solver still has to charge
its actual host operations to this combined budget.
-/

namespace ThreeSum.ArithmeticStageBounds

open Filter Real Parameters Scales BandScales CostLedger HierarchyScales
  MassScales StageBounds UniformStageBounds ModuloCosts
open scoped Topology

set_option maxHeartbeats 1000000























theorem bits_le_window_square (n : ℕ) : inputBits n+1 ≤ primeWindow n^2 := by
  have hroot := Nat.lt_succ_sqrt' (inputBits n)
  have hpow : Nat.sqrt (inputBits n)+1 ≤ 2^(Nat.sqrt (inputBits n)+1) :=
    (Nat.lt_pow_self (by decide : 1 < 2)).le
  have hs := Nat.pow_le_pow_left hpow 2
  unfold primeWindow windowExponent
  simp only [Nat.succ_eq_add_one] at hroot
  omega

theorem remainder_bits_le {n : ℕ} (k : ℕ) (hn : 0 < n) :
    Nat.log 2 (n^k+1)+1 ≤ bitBudget k n := by
  have hp : 0 < n^k := Nat.pow_pos hn
  have hm := Nat.log_mono_right (b := 2) (show n^k+1 ≤ 3*n^k by omega)
  have hl := log2_difference_bound k hn
  rw [Nat.log2_eq_log_two] at hl
  have hw := Nat.mul_le_mul_left (2*(k+2)) (bits_le_window_square n)
  unfold bitBudget
  omega

theorem invocation_le_budget {n p nA nB nC : ℕ} (k : ℕ)
    (hn : 0 < n) (hp : p ≤ maxMod n)
    (ha : nA ≤ bandSize n) (hb : nB ≤ bandSize n) (hc : nC ≤ bandSize n) :
    LightModuloCounts.time p nA nB nC (n^k) ≤ perTripleBudget k n := by
  have ht := ModuloRuntime.time_mono hp nA nB nC (n^k)
  have hbnd := ModuloCosts.time_bound (maxMod n) nA nB nC (bandSize n) (n^k) ha hb hc
  have hm := Nat.mul_le_mul_left (bandSize n) (remainder_bits_le k hn)
  unfold perTripleBudget
  omega

noncomputable section

theorem powerBound_mono {f g : ℕ → ℕ} {a : ℝ} (hg : PowerBound g a)
    (hfg : ∀ᶠ n : ℕ in atTop, f n ≤ g n) : PowerBound f a := by
  intro d hd
  filter_upwards [hg d hd, hfg] with n hn hm
  exact (show (f n : ℝ) ≤ (g n : ℝ) by exact_mod_cast hm).trans hn



























theorem window_powerBound : PowerBound primeWindow 0 :=
  PowerBound.of_rate primeWindow_log_ratio_tendsto_zero

theorem maxMod_powerBound : PowerBound maxMod ((E+1/2)/5) := by
  change PowerBound (fun n => radix n*(4*primeWindow n)^2) ((E+1/2)/5)
  have hwindow := ((PowerBound.const 4).mul window_powerBound).pow 2
  have hh := (PowerBound.of_rate radix_log_ratio_tendsto).mul hwindow
  simpa only [zero_add, mul_zero, add_zero] using hh







theorem bitBudget_powerBound (k : ℕ) : PowerBound (bitBudget k) 0 := by
  have hh := (PowerBound.const (2*(k+2))).mul (window_powerBound.pow 2)
  have hh' : PowerBound (fun n => 2*(k+2)*primeWindow n^2) 0 := by
    simpa only [Nat.cast_ofNat, mul_zero, add_zero] using hh
  exact hh'.add_same (PowerBound.const 1)












































theorem identity_powerBound : PowerBound (fun n : ℕ => n) 1 := by
  intro d hd
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  simpa only [Real.rpow_one] using
    (Real.rpow_le_rpow_of_exponent_le hnR (show (1 : ℝ) ≤ 1+d by linarith))



























end
end ThreeSum.ArithmeticStageBounds

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
# Evaluating a whole list of one-hot mask hashes

This wrapper builds the powers table itself, hashes each stored mask, and
writes the raw nonnegative values. It is shared by the local-cover matrix
construction and input-source encoding. The cost is linear in the number
of masks times their width; no evaluation oracle is assumed.
-/

namespace ThreeSum.LightMaskHashes

open Light LightSubsetAddress

set_option maxHeartbeats 1000000



















variable {lim : Limits} {P : Program} {d : ℕ}









































































































theorem time_bound (L n : ℕ) : time L n ≤ 300*(L+1)*(n+1) := by
  unfold time powTableTime LightOneHot.time
  nlinarith

end ThreeSum.LightMaskHashes

end

section


/-!
# Computing one complete row of signed local output keys

For every stored output mask, this fixed program sums the true and false
coefficients outside that mask and subtracts the two sums. It constructs
its own zero row and powers table. Both input coefficient rows and the
literal output-mask enumeration remain intact.
-/

namespace ThreeSum.LightLocalKeyRow

open Light LightSubsetAddress

set_option maxHeartbeats 2400000
set_option maxRecDepth 10000





























variable {lim : Limits} {P : Program} {d : ℕ}

































































































theorem time_bound (L n : ℕ) : time L n ≤ 950*(L+1)*(n+1) := by
  have h := LightMaskHashes.time_bound L n
  unfold time fillTime LightArray.linearTime
  nlinarith

end ThreeSum.LightLocalKeyRow

end

section


/-!
# Complete occurrence-by-output local key array

The loop reads the two stored coefficient rows for each schedule occurrence,
constructs every signed local output key, and copies that row into the final
contiguous array. It reuses the row scratch and preserves earlier rows.
-/

namespace ThreeSum.LightLocalKeys

open Light

set_option maxHeartbeats 2500000
set_option maxRecDepth 10000


























variable {lim : Limits} {P : Program} {d : ℕ}






























































































theorem time_bound (L n rows : ℕ) : time L n rows ≤ 1200*(L+1)*(n+1)*(rows+1) := by
  have hh := LightLocalKeyRow.time_bound L n
  have hper : LightLocalKeyRow.time L n+copyTime n+130 ≤ 1100*(L+1)*(n+1) := by
    unfold copyTime
    nlinarith
  have hm := Nat.mul_le_mul_left rows hper
  have he : 1200*(L+1)*(n+1)*(rows+1) = rows*(1100*(L+1)*(n+1))+20+
      (100*rows*(L+1)*(n+1)+1200*L*n+1200*L+1200*n+1180) := by ring
  unfold time
  rw [he]
  omega

end ThreeSum.LightLocalKeys

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






/-! ## Tasks and solvers -/

































































theorem le_timeUpTo (Tn : ℕ → ℕ → ℕ) (n : ℕ) {U : ℕ} {u : ℝ} (hu : (U : ℝ) ≤ u) :
    (Tn n U : ℝ) ≤ timeUpTo Tn n u :=
  Nat.cast_le.2 (Finset.le_sup (f := Tn n)
    (Finset.mem_range.2 (Nat.lt_succ_of_le (Nat.le_floor hu))))

/-- What bounds the time for every natural number `U ≤ u` bounds `timeUpTo`.  For a negative `u`
there is still `U = 0`. -/
theorem timeUpTo_le {Tn : ℕ → ℕ → ℕ} {n : ℕ} {u B : ℝ}
    (h : ∀ U : ℕ, (U : ℝ) ≤ max u 0 → (Tn n U : ℝ) ≤ B) : timeUpTo Tn n u ≤ B := by
  obtain ⟨U, hU, hsup⟩ := Finset.exists_mem_eq_sup (Finset.range (⌊u⌋₊ + 1))
    ⟨0, Finset.mem_range.2 (Nat.succ_pos _)⟩ (Tn n)
  rw [timeUpTo, hsup]
  refine h U ((Nat.cast_le.2 (Nat.lt_succ_iff.1 (Finset.mem_range.1 hU))).trans ?_)
  rcases le_total 0 u with hu | hu
  · exact (Nat.floor_le hu).trans (le_max_left u 0)
  · rw [Nat.floor_of_nonpos hu, Nat.cast_zero]
    exact le_max_right u 0

/-- A solver with a polynomially bounded need solves its task in its own time. -/
theorem Solves.solvedIn {task : Task} {P : Program} {p : ℕ} {Tn : ℕ → ℕ → ℕ} {need : ℕ → ℕ → Need}
    (hs : Solves task P p Tn need) (hp : PolyNeed need) : SolvedIn task (timeUpTo Tn) :=
  ⟨P, p, Tn, need, hp, hs, fun n _ _ _ _ hu => le_timeUpTo Tn n hu⟩

/-! ## Hosts -/






















/-! ## Tasks with a list of parameters -/














































end Light

end
end

section


/-!
# Charge the executed common-prime setup

The bound includes the generated pool, every aggregate candidate minimum,
all original band-score calls, and the computed chain depth. The size-only
budget uses the same quadratic owner bound as the physical mass theorem.
-/

namespace ThreeSum.BandPrimeCosts

open Scales BandScales CostLedger ArithmeticStageBounds

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000

















































































theorem unit_le_budget {n : ℕ} (k : ℕ) (hn : 0 < n) :
    unit (maxMod n) (bandSize n) (n^k) ≤ 3*perTripleBudget k n := by
  have hc := invocation_le_budget (p := maxMod n) k hn le_rfl le_rfl le_rfl le_rfl
  have hp := (KaratsubaInterface.le_capacity (maxMod n)).trans (ModuloCosts.capacity_le_roundedPower (maxMod n))
  have hl : Nat.log 2 (maxMod n+1) ≤ maxMod n+1 := Nat.log_le_self _ _
  have hj : LightWeightedScore.jointTime (maxMod n) ≤ perTripleBudget k n := by
    unfold LightWeightedScore.jointTime LightResidues.residueBudget perTripleBudget
    omega
  have hlarge : 1000 ≤ perTripleBudget k n := by unfold perTripleBudget; omega
  unfold unit
  omega





















end ThreeSum.BandPrimeCosts

end

section


/-!
# Exponent bound for the actual common-prime setup budget

The candidate pool and number of minimum rounds contribute only a
subpolynomial factor. This proves the arithmetic term for the executed
aggregate program; it does not assert completion of the whole solver.
-/

namespace ThreeSum.BandPrimeCosts

open Filter Real Scales BandScales CostLedger Parameters StageBounds HierarchyScales
  ArithmeticStageBounds
open scoped Topology

set_option maxHeartbeats 1400000

noncomputable section























theorem owner_count_powerBound :
    PowerBound (fun n => 3*bandCount n^2+1) (2*(1-(E+bandShift)/5)) := by
  have hc := (PowerBound.const 3).mul ((PowerBound.of_rate bandCount_log_rate).pow 2)
  have hc' : PowerBound (fun n => 3*bandCount n^2) (2*(1-(E+bandShift)/5)) := by
    simpa only [Nat.cast_ofNat,zero_add] using hc
  have he : (0 : ℝ) ≤ 2*(1-(E+bandShift)/5) := by
    have hh := E_bounds.2
    unfold bandShift
    linarith
  exact hc'.add_same ((PowerBound.const 1).mono_exponent he)


















theorem timeBudget_certificate (k : ℕ) : PowerBound (timeBudget k) certificateExponent :=
  (timeBudget_powerBound k).mono_exponent (all_costs_le_certificate _ (by simp [costLedger]))












end
end ThreeSum.BandPrimeCosts

end

section


/-!
# Output-sensitive subset-layer enumeration in the benchmark language

The recursive routine writes into consecutive output cells. Empty layers
return immediately; a zero-cardinality layer emits one mask. The two
recursive children share the output buffer and write adjacent, disjoint
segments. No ambient Boolean cube is scanned and no output list is copied.
-/

namespace ThreeSum.LightSubsetEnumeration

open Light ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program}












































theorem time_bound (L k : ℕ) :
    time L k ≤ 150*((4*L+1)*L.choose k+1) := by
  exact Nat.mul_le_mul_left 150 (enumerationWork_bound L k)



























































































































































end ThreeSum.LightSubsetEnumeration

end

section


/-!
# A fixed subset-layer enumerator with its own power-table construction

The main theorem has no supplied lookup-table correctness assumption. The
only auxiliary memory is a table of `L+1` powers of two, built once before
the recursive enumeration. The output has exactly `L.choose k` cells.
-/

namespace ThreeSum.LightSubsetEnumerationSetup

open Light ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program}


































































theorem time_bound (L k : ℕ) : time L k ≤ 800*(L+1)*(L.choose k+1) := by
  have h := LightSubsetEnumeration.time_bound L k
  unfold time powTableTime
  nlinarith

end ThreeSum.LightSubsetEnumerationSetup

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











































theorem cutoff_eq (n : ℕ) :
    2*microHalf (inputBits n)*blockCount (inputBits n) = mu n := by
  unfold mu totalSize microSize microHalf
  ring




























































end ThreeSum.BlockSourceSharing

end

section


/-!
# Exact natural quotient by a small counting loop

This helper is used for size parameters whose numerator is logarithmic in
the original input length. Its time is linear in the quotient, explicitly
charged below. A zero divisor returns zero, matching natural division.
-/

namespace ThreeSum.LightSmallDivide

open Light

variable {lim : Limits} {P : Program} {d : ℕ}






































































theorem time_bound (a b : ℕ) : time a b ≤ 20*a+40 := by
  have h := Nat.div_le_self a b
  unfold time
  omega

end ThreeSum.LightSmallDivide

end

section


/-!
# From selected coefficient rows to every original global output key

The fixed program constructs the output-mask layer, all signed local keys,
and the full positional product. Its output is the literal occurrence-aware
`GlobalKeyEnumeration.globalKeys` array. No input key or mask table is assumed.
-/

namespace ThreeSum.LightGlobalKeys

open Light GlobalEncoding GlobalKeyEnumeration LocalHashMoments LocalCoverBounds
open LightSubsetAddress SubsetAddress

set_option maxHeartbeats 600000
set_option maxRecDepth 10000










































theorem localCount_pos (h : ℕ) : 0 < localCount h := by
  apply Nat.mul_pos
  · unfold scheduleSize scheduleLength
    positivity
  · exact Nat.choose_pos (by omega)





















variable {lim : Limits} {P : Program} {d : ℕ}





























































































































theorem time_bound (h J : ℕ) :
    time h J ≤ 2000*(512*h+1)*(outputCount (512*h) h+1)*(scheduleSize h+1)+
      300*(J+1)*(localCount h^J+1)+200 := by
  have he := LightSubsetEnumerationSetup.time_bound (512*h) (2*h)
  have hl := LightLocalKeys.time_bound (512*h) (outputCount (512*h) h) (scheduleSize h)
  have hg := LightRadixKeys.time_bound (localCount h) J (localCount_pos h)
  have hc : 800*(512*h+1)*(outputCount (512*h) h+1) ≤
      800*(512*h+1)*(outputCount (512*h) h+1)*(scheduleSize h+1) :=
    Nat.le_mul_of_pos_right _ (by omega)
  change LightSubsetEnumerationSetup.time (512*h) (2*h) ≤
    800*(512*h+1)*(outputCount (512*h) h+1) at he
  unfold time
  nlinarith

end ThreeSum.LightGlobalKeys

end

section


/-!
# Actual construction of the three lifted original A-key arrays

The middle row is computed by the checked signed remainder routine. Two
affine scans append the minus and plus lifts. Every original position is
retained in each row, and the resulting segment is the exact guarded-key
list whose balancing bound is proved in `RawAKeyLists`.
-/

namespace ThreeSum.LightRawAKeys

open Light LightResidues RawIncidences RawAKeyLists

set_option maxHeartbeats 1000000
set_option maxRecDepth 6000













variable {lim : Limits} {P : Program} {d : ℕ}




























































































theorem time_bound (n U : ℕ) : time n U ≤ 220*(n+1)*(Nat.log 2 (U+1)+1) := by
  unfold time residuesTime residueBudget LightReportingAffine.time
  nlinarith

end ThreeSum.LightRawAKeys

end

section


/-!
# Building the color of every original array position

The program constructs its own binary-power table and evaluates one selected
two-coordinate coloring on every index. No index-bit or coloring oracle is
part of the input. Memory outside the output colors and scratch is preserved.
-/

namespace ThreeSum.LightColorArray

open Light LightSubsetAddress

set_option maxHeartbeats 1200000


















variable {lim : Limits} {P : Program} {d : ℕ}















































































theorem time_bound (W n : ℕ) : time W n ≤ 600*(W+1)*(n+1) := by
  unfold time powTableTime LightColorIndex.time LightMaskErase.time
  nlinarith

end ThreeSum.LightColorArray

end

section


/-!
# Original-array construction of all three color classes

A fixed six-procedure program builds the color array and extracts three
disjoint output segments with length headers. The third class is negated.
Original values and their multiplicities are kept until class normalization.
-/

namespace ThreeSum.LightColorClasses

open Light ColorClassLists

set_option maxHeartbeats 1500000
set_option maxRecDepth 10000



































variable {lim : Limits} {P : Program} {d : ℕ}






































































































theorem time_bound (W n : ℕ) : time W n ≤ 1200*(W+1)*(n+1) := by
  have h := LightColorArray.time_bound W n
  unfold time LightClassFilter.time
  nlinarith

end ThreeSum.LightColorClasses

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


































variable {lim : Limits} {P : Program} {d : ℕ}



















































































































theorem time_bound (W n g : ℕ) :
    time W n g ≤ 1200*(W+1)*(n+1)+ColorBandBounds.time n g+300 := by
  have h := LightColorClasses.time_bound W n
  unfold time
  omega

end ThreeSum.LightColorBands

end

section


/-!
# Original input to the retained owner and A-incidence catalog

The selected index coloring, class extraction, normalization, endpoint
construction, three rectangular owner tables, four-cell owner records, and
packed A-incidence rows are all executed by this fixed program. The rows
retain physical owner identities and sorted-array coordinates. Membership
in the original color classes is retained separately by `Represents`.
-/

namespace ThreeSum.LightBandRawAColor

open Light BandPartition BandCandidateRows BandRawA ColorClassLists

set_option maxHeartbeats 2400000
set_option maxRecDepth 11000




































































variable {lim : Limits} {P : Program} {d : ℕ}























































































































































theorem time_bound (W n g : ℕ) :
    time W n g ≤ 1200*(W+1)*(n+1)+ColorBandBounds.time n g+catalogTime n g+600 := by
  have h := LightColorBands.time_bound W n g
  unfold time
  omega

end ThreeSum.LightBandRawAColor

end

section


/-! # Finite charge of the actual original-band histogram and bucket catalog -/

namespace ThreeSum.SourceBandCosts

open Scales TrimScales StageBounds CostLedger BandScales LocalCoverBounds








































































































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































end ThreeSum.SourceBandCosts

end

section


/-! # Original-size resource envelope for the actual source-header adapter -/

namespace ThreeSum.EncodedColorSourcesCosts

open Scales TrimScales BandScales











theorem time_eq (n p U M : ℕ) :
    time n p U M=SourceFiniteCosts.time n p U M+20*blockCount (inputBits n)+1020 := by
  unfold time LightNatPower.time
  omega

end ThreeSum.EncodedColorSourcesCosts

end

section


/-!
# Actual initialization of the integer block schedule

The fixed program computes all initial size parameters from the input
length. It uses the benchmark's proved logarithm, ceiling cube-root and
ceiling-half loops, with exact rounding bridges below. Division is used
only through an actual counting routine on the logarithmic numerator.
-/

namespace ThreeSum.LightScales

open Light ThreeSum.Scales

variable {lim : Limits} {P : Program}




theorem root_le_self (m : ℕ) : Nat.nthRoot 3 m ≤ m :=
  (Nat.le_self_pow (by decide : 3 ≠ 0) (Nat.nthRoot 3 m)).trans
    (Nat.pow_nthRoot_le (Or.inl (by decide : 3 ≠ 0)))




theorem microHalf_le_self (m : ℕ) : microHalf m ≤ m :=
  (Nat.div_le_self (Nat.nthRoot 3 m) 2).trans (root_le_self m)

theorem blockCount_le (m : ℕ) : blockCount m ≤ 20*m :=
  Nat.mul_le_mul_left 20 (Nat.div_le_self m (100*microSize m))





































































































































theorem time_bound (n : ℕ) : time n ≤ 500*(inputBits n+1) := by
  have hu := cbrtLeast_le_self (inputBits n+1)
  have hh := Nat.div_le_self (cbrtLeast (inputBits n+1)+1) 2
  have hq := Nat.div_le_self (inputBits n) (100*muZero n)
  unfold time log2Time cbrtCeilTime halfTime LightSmallDivide.time
  simp only [inputBits,Nat.log2_eq_log_two] at *
  omega






















end ThreeSum.LightScales

end

section


/-!
# Executing global powers and rounded band sizes

This routine consumes the already computed local output count, local prime,
block count, and total inner size. All global powers, the square-root
rounding, and the final ceiling division are actual Light computations.
The square-root loop and quotient loop are included in the stated time.
-/

namespace ThreeSum.LightGlobalSizes

set_option maxHeartbeats 1000000

open Light LocalCoverBounds








































variable {lim : Limits} {P : Program} {d : ℕ}








































































































theorem time_bound (C J mu : ℕ) :
    time C J mu ≤ 1000*(J+mu+root C J+divisor mu+1) := by
  have he := Nat.div_le_self mu 20
  have hb := Nat.div_le_self (numerator C J mu) (divisor mu)
  have hn : numerator C J mu ≤ root C J+divisor mu := Nat.sub_le _ _
  have hs : Nat.sqrt (C^J-1) ≤ root C J := by unfold root rootCeiling; omega
  unfold time LightNatPower.time LightSmallDivide.time sqrtTime
  omega






theorem localCount_pow (n : ℕ) :
    localCount n ^ Scales.blockCount (Scales.inputBits n) = Scales.typedOutputs n := by
  have hwidth : 256*Scales.muZero n = 512*Scales.microHalf (Scales.inputBits n) := by
    rw [Scales.muZero_eq_twice_half]
    ring
  unfold Scales.typedOutputs
  rw [hwidth,Scales.muZero_eq_twice_half]
  rfl








end ThreeSum.LightGlobalSizes

end

section


/-! # Actual finite budgets of the retained common-prime stage -/

namespace ThreeSum.EncodedColorPrimeCosts

open Light Scales BandScales CostLedger ArithmeticStageBounds

theorem core_time_eq (maxMod g R M y U : ℕ) :
    LightEncodedColorPrimeCore.time maxMod g R M y U=
      LightBandPrimeSetup.time maxMod g R M y U+760 := by
  unfold LightEncodedColorPrimeCore.time LightBandPrimeSetup.time LightBandPrimeConstruction.time
  omega

theorem time_eq (maxMod nA nB nC g M y U : ℕ) :
    LightEncodedColorPrime.time maxMod nA nB nC g M y U=
      LightBandPrimeSetup.time maxMod g (LightEncodedColorPrime.count nA nB nC g) M y U+1160 := by
  rw [LightEncodedColorPrime.time,core_time_eq]























theorem count_le {nA nB nC n : ℕ} (ha : nA ≤ n) (hb : nB ≤ n) (hc : nC ≤ n) :
    LightEncodedColorPrime.count nA nB nC (bandSize n) ≤ 3*bandCount n^2 := by
  have a := SourceBandCosts.size_le_bandCount ha
  have b := SourceBandCosts.size_le_bandCount hb
  have c := SourceBandCosts.size_le_bandCount hc
  have ab := Nat.mul_le_mul a b
  have ac := Nat.mul_le_mul a c
  have bc := Nat.mul_le_mul b c
  unfold LightEncodedColorPrime.count
  nlinarith

theorem time_le_budget {nA nB nC n : ℕ} (k : ℕ) (hn : 0 < n)
    (ha : nA ≤ n) (hb : nB ≤ n) (hc : nC ≤ n) :
    LightEncodedColorPrime.time (maxMod n) nA nB nC (bandSize n) (radix n) (primeWindow n) (n^k) ≤
      BandPrimeCosts.timeBudget k n+1160 := by
  rw [time_eq]
  exact Nat.add_le_add_right (BandPrimeCosts.setup_time_le_budget k hn (count_le ha hb hc)) 1160


































end ThreeSum.EncodedColorPrimeCosts

end

section


/-!
# Exponent of the complete shared-catalog invocation budget

The local balanced-pair enumeration and all polynomial factors in the
concrete52-procedure constructor have exponent zero. Multiplying the
existing box ledger by this overhead therefore preserves its exponent.
This charges catalog invocations; the surrounding bank iterator is separate.
-/

namespace ThreeSum.SharedReportingCosts

open Filter Real Scales Parameters StageBounds ArithmeticStageBounds
open scoped Topology

set_option maxHeartbeats 1500000

noncomputable section

theorem bits_powerBound : PowerBound inputBits 0 := by
  have hh : PowerBound (fun n => primeWindow n^2) 0 := by
    simpa only [mul_zero] using window_powerBound.pow 2
  exact powerBound_mono hh (Eventually.of_forall fun n => by
    have h := bits_le_window_square n
    omega)

theorem half_powerBound : PowerBound _root_.ThreeSum.SharedReportingCosts.half 0 :=
  powerBound_mono bits_powerBound (Eventually.of_forall fun n =>
    LightScales.microHalf_le_self (inputBits n))

theorem blocks_powerBound : PowerBound _root_.ThreeSum.SharedReportingCosts.blocks 0 := by
  have hh : PowerBound (fun n => 20*inputBits n) 0 := by
    simpa only [zero_add] using (PowerBound.const 20).mul bits_powerBound
  exact powerBound_mono hh (Eventually.of_forall fun n =>
    LightScales.blockCount_le (inputBits n))

theorem local_width_powerBound : PowerBound localWidth 0 := by
  change PowerBound (fun n => 512*_root_.ThreeSum.SharedReportingCosts.half n) 0
  simpa only [zero_add] using (PowerBound.const 512).mul half_powerBound

theorem width_powerBound : PowerBound width 0 := by
  change PowerBound (fun n => _root_.ThreeSum.SharedReportingCosts.blocks n*localWidth n) 0
  simpa only [zero_add] using blocks_powerBound.mul local_width_powerBound






































end
end ThreeSum.SharedReportingCosts

end

section


/-! # Uniform finite and exponent bounds for the actual switch controls -/

namespace ThreeSum.LightSwitchCosts

open Scales StageBounds ArithmeticStageBounds Filter
open scoped Topology


























































noncomputable section

theorem time_powerBound : PowerBound timeBudget 0 := by
  have hh := ((PowerBound.const 100).mul
    (SharedReportingCosts.bits_powerBound.add_same (PowerBound.const 1)))
  have hh' : PowerBound (fun n => 100*(inputBits n+1)) 0 := by
    simpa only [zero_add] using hh
  exact hh'.add_same (PowerBound.const 50)

theorem depth_powerBound : PowerBound depthBudget 0 := by
  have hh : PowerBound (fun n => 5200*inputBits n) 0 := by
    simpa only [zero_add] using (PowerBound.const 5200).mul SharedReportingCosts.bits_powerBound
  exact hh.add_same (PowerBound.const 90)














end
end ThreeSum.LightSwitchCosts

end

section


/-!
# Charge the executed shared catalog bank, including every surrounding loop

The exact sum of level costs is preserved. Actual switch evaluation,
downset sizing, address arithmetic, row iteration, and the one-time depth
and Pascal initializers add only a factor of exponent zero to the existing
shared-box ledger. The bank is indexed by occurrence and two bands alone.
-/

namespace ThreeSum.SharedReportingBankCosts

open Scales Parameters StageBounds ArithmeticStageBounds CostLedger Filter
open SharedReportingCosts
open scoped Topology

set_option maxHeartbeats 2200000
set_option maxRecDepth 12000
































































































noncomputable section

theorem round_extra_powerBound : PowerBound roundExtra 0 := by
  have hw := SharedReportingCosts.width_powerBound.add_same (PowerBound.const 1)
  have hpoly : PowerBound (fun n => 1400*(width n+1)^2) 0 := by
    simpa only [mul_zero,zero_add] using (PowerBound.const 1400).mul (hw.pow 2)
  exact (LightSwitchCosts.time_powerBound.add_same hpoly).add_same (PowerBound.const 2808)

theorem round_overhead_powerBound : PowerBound roundOverhead 0 :=
  SharedReportingCosts.overhead_powerBound.add_same round_extra_powerBound

theorem setup_powerBound : PowerBound setup 0 := by
  have hw := SharedReportingCosts.local_width_powerBound.add_same (PowerBound.const 1)
  have hpoly : PowerBound (fun n => 1500*(localWidth n+1)^2) 0 := by
    simpa only [mul_zero,zero_add] using (PowerBound.const 1500).mul (hw.pow 2)
  exact (LightSwitchCosts.depth_powerBound.add_same hpoly).add_same (PowerBound.const 3300)

theorem overhead_powerBound : PowerBound overhead 0 :=
  (round_overhead_powerBound.add_same (PowerBound.const 1600)).add_same setup_powerBound

theorem budget_powerBound : PowerBound budget (2-epsilon*boxSaving) := by
  have hconst : PowerBound (fun _ : ℕ => 1) (2-epsilon*boxSaving) :=
    (PowerBound.const 1).mono_exponent (by norm_num [epsilon,boxSaving])
  change PowerBound (fun n => overhead n*(boxCount n+1)) (2-epsilon*boxSaving)
  simpa only [zero_add] using overhead_powerBound.mul (boxes_powerBound.add_same hconst)

theorem budget_certificate : PowerBound budget certificateExponent :=
  budget_powerBound.mono_exponent (all_costs_le_certificate _ (by simp [costLedger]))






end
end ThreeSum.SharedReportingBankCosts

end

section


/-!
# Polynomial limits for the actual shared reporting host

The finite word, cell, and depth formulas are bounded at every input size.
The resulting `Need` includes the complete executed host, while its time
bound remains the exact shared-box budget proved separately.
-/

namespace ThreeSum.SharedReportingBankResourceBounds

open Scales StageBounds Filter Light
open scoped Topology

set_option maxHeartbeats 1200000
set_option maxRecDepth 14000

noncomputable section

theorem bits_power_powerBound : PowerBound (fun n => 2^(inputBits n)) 1 := by
  apply ArithmeticStageBounds.powerBound_mono ArithmeticStageBounds.identity_powerBound
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  simpa only [inputBits,Nat.log2_eq_log_two] using
    Nat.pow_log_le_self 2 (by omega : n ≠ 0)

theorem magnitude_powerBound : PowerBound magnitude 2048 := by
  have hh := (PowerBound.const (2^2048)).mul (bits_power_powerBound.pow 2048)
  have he : magnitude = fun n => 2^2048*(2^(inputBits n))^2048 := by
    funext n
    unfold magnitude
    rw [show 2048*(inputBits n+1)=2048+inputBits n*2048 by omega,pow_add,pow_mul]
  rw [he]
  simpa only [Nat.cast_ofNat,mul_one,zero_add] using hh













































end
end ThreeSum.SharedReportingBankResourceBounds

end

section


/-! # Finite and asymptotic cost of executing the small coloring family -/

namespace ThreeSum.LightColorParametersCosts

open ColorParameters Scales StageBounds























open Filter Real
open scoped Topology

noncomputable section

theorem width_powerBound : PowerBound width 0 :=
  SharedReportingCosts.bits_powerBound.add_same (PowerBound.const 1)

theorem count_powerBound : PowerBound (fun n => count (width n)) 0 := by
  simpa only [count,mul_zero,zero_add] using (PowerBound.const 81).mul (width_powerBound.pow 2)













end
end ThreeSum.LightColorParametersCosts

end

section


/-!
# The complete local-cover program fits the uniform local-search budget

Every bound below is for the actual fixed program, including mask and
coefficient construction, counting division, histograms, matrix assembly,
the original greedy loop, and selected-row gathering.
-/

namespace ThreeSum.LightLocalCoverResources

open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables
open LightLocalCoverLayout LightLocalCoverMagnitude

set_option maxHeartbeats 1800000



theorem setup_time_polynomial {h B : ℕ} (H : Bounds h B) :
    LightLocalCoverSetup.time h ≤ 11000*B^5 := by
  have hbuild := LightLocalCoverCost.build_time_bound H.positive H.width H.vertices H.prime H.candidates H.rounds
  have hp2 : cols h ≤ B^2 := by
    have hp := Nat.pow_le_pow_left H.prime 2
    unfold cols
    nlinarith
  have hlog := Nat.log_le_self 2 (cols h)
  have hB : 1 ≤ B := H.positive
  have hL := H.width
  have hpow15 := Nat.le_self_pow (by decide : 5 ≠ 0) B
  have hpow25 := Nat.pow_le_pow_right hB (by decide : 2 ≤ 5)
  have hB5 : 1 ≤ B^5 := Nat.pow_pos (by omega)
  unfold LightLocalCoverSetup.time LightNatPower.time log2Time
  omega














































































































theorem time_bound (h : ℕ) : LightLocalCoverSetup.time h ≤ envelope h := by
  have hs : 1 ≤ (h+1)^2 := Nat.pow_pos (by omega)
  calc
    _ ≤ 11000*(magnitude h)^5 := setup_time_polynomial (bounds h)
    _ ≤ 2^14*(magnitude h)^5 := Nat.mul_le_mul_right _ (by decide)
    _ = 2^(14+600000*(h+1)^2*5) := by rw [magnitude,← pow_mul,← pow_add]
    _ ≤ envelope h := Nat.pow_le_pow_right (by decide) (by omega)






































































end ThreeSum.LightLocalCoverResources

end

section


/-! # Resource bounds for the complete h-and-free local-cover initializer -/

namespace ThreeSum.LightLocalCoverInitResources

open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables
open LightLocalCoverLayout

set_option maxHeartbeats 1500000



theorem parameters_envelope_le (h : ℕ) :
    LocalParameterBounds.envelope h ≤ LightLocalCoverResources.envelope h := by
  unfold LocalParameterBounds.envelope LightLocalCoverResources.envelope
  apply Nat.pow_le_pow_right (by decide)
  nlinarith only [Nat.zero_le (h*h)]

theorem constant_le (h : ℕ) : 600 ≤ LightLocalCoverResources.envelope h := by
  have hs : 1 ≤ (h+1)^2 := Nat.pow_pos (by omega)
  exact (by decide : 600 ≤ 2^10).trans
    (Nat.pow_le_pow_right (by decide) (by omega))

theorem four_envelope_le (h : ℕ) :
    4*LightLocalCoverResources.envelope h ≤ envelope h := by
  have hs : 1 ≤ (h+1)^2 := Nat.pow_pos (by omega)
  calc
    _ = 2^2*2^(4000000*(h+1)^2) := rfl
    _ = 2^(2+4000000*(h+1)^2) := (pow_add _ _ _).symm
    _ ≤ envelope h := Nat.pow_le_pow_right (by decide) (by omega)

theorem metadata_time_le (h : ℕ) :
    LightLocalCoverMetadata.time h ≤ LightLocalCoverSetup.time h+500 := by
  unfold LightLocalCoverMetadata.time LightLocalCoverSetup.time
  omega

theorem time_bound (h : ℕ) : LightLocalCoverInit.time h ≤ envelope h := by
  have hp := (LocalParameterBounds.time_bound h).trans (parameters_envelope_le h)
  have hc := LightLocalCoverResources.time_bound h
  have hm := metadata_time_le h
  have hk := constant_le h
  apply (show LightLocalCoverInit.time h ≤ 4*LightLocalCoverResources.envelope h from ?_).trans
    (four_envelope_le h)
  unfold LightLocalCoverInit.time
  omega
























theorem envelope_le_search {n : ℕ} (hh : 1 ≤ Scales.microHalf (Scales.inputBits n)) :
    envelope (Scales.microHalf (Scales.inputBits n)) ≤ Scales.localSearch 5000000 n := by
  unfold envelope Scales.localSearch
  rw [Scales.muZero_eq_twice_half]
  apply Nat.pow_le_pow_right (by decide)
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_left
  omega


























































end ThreeSum.LightLocalCoverInitResources

end

section


/-! # A proved polynomial scale for the selected-color program's dimensions -/

namespace ThreeSum.EncodedColorResources

open Scales BandScales ArithmeticStageBounds StageBounds GlobalEncoding LocalCoverBounds
open Filter

set_option maxHeartbeats 2200000
set_option maxRecDepth 13000








theorem scale_bounds (n : ℕ) : 100 ≤ scale n ∧ n+1 ≤ scale n ∧
    SharedReportingBankResourceBounds.magnitude n ≤ scale n ∧ localEnvelope n ≤ scale n ∧
    maxMod n ≤ scale n ∧ primeWindow n ≤ scale n := by
  unfold scale
  omega

theorem local_bounds (n : ℕ) : LightLocalCoverMagnitude.Bounds (_root_.ThreeSum.EncodedColorResources.half n) (scale n) := by
  have hm : LightLocalCoverMagnitude.magnitude (_root_.ThreeSum.EncodedColorResources.half n) ≤ localEnvelope n := by
    unfold LightLocalCoverMagnitude.magnitude localEnvelope LightLocalCoverInitResources.envelope
    exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (by decide : 600000 ≤ 5000000))
  have hs := hm.trans (scale_bounds n).2.2.2.1
  have H := LightLocalCoverMagnitude.bounds (_root_.ThreeSum.EncodedColorResources.half n)
  exact ⟨H.positive.trans hs,H.width.trans hs,H.vertices.trans hs,H.prime.trans hs,
    H.cap.trans hs,H.candidates.trans hs,H.rounds.trans hs,H.decodePower.trans hs,H.maskPower.trans hs⟩

















theorem powers (n : ℕ) : 2^(width n+1) ≤ scale n ∧
    LightBlockSourceCatalog.count (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum.EncodedColorResources.blocks n) ≤ scale n ∧
    localPrime (_root_.ThreeSum.EncodedColorResources.half n)^(_root_.ThreeSum.EncodedColorResources.blocks n)*localPrime (_root_.ThreeSum.EncodedColorResources.half n) ≤ scale n ∧
    2^(_root_.ThreeSum.EncodedColorResources.blocks n) ≤ scale n := by
  have H := SharedReportingBankResourceBounds.components n
  have hm := (scale_bounds n).2.2.1
  refine ⟨H.widthPower.trans hm,H.occurrence.trans hm,H.primePower.trans hm,?_⟩
  have htwo : (2 : ℕ) ≤ 2^(512*_root_.ThreeSum.EncodedColorResources.half n)+1 := by have hh := Nat.two_pow_pos (512*_root_.ThreeSum.EncodedColorResources.half n); omega
  exact (Nat.pow_le_pow_left htwo (_root_.ThreeSum.EncodedColorResources.blocks n)).trans (H.radixPower.trans hm)

theorem modulus_le (n : ℕ) : BlockSourceEncoding.modulus (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum.EncodedColorResources.blocks n) ≤ scale n := by
  exact (Nat.le_mul_of_pos_right _ (localPrime_pos (_root_.ThreeSum.EncodedColorResources.half n))).trans (powers n).2.2.1

theorem endpoint_le (n : ℕ) : LightBlockSourceBuild.endpointBound (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum.EncodedColorResources.blocks n) ≤ (scale n)^2 := by
  have hw : width n ≤ scale n := by have hh := (dimensions n).1; omega
  have hh := Nat.mul_le_mul hw (powers n).2.2.1
  simpa only [LightBlockSourceBuild.endpointBound,width,BlockSourceEncoding.modulus,pow_two] using hh

theorem radix_power_le (n : ℕ) : (localPrime (_root_.ThreeSum.EncodedColorResources.half n)+1)^(_root_.ThreeSum.EncodedColorResources.blocks n) ≤ (scale n)^2 := by
  have hp := localPrime_pos (_root_.ThreeSum.EncodedColorResources.half n)
  have hmod := modulus_le n
  calc
    _ ≤ (2*localPrime (_root_.ThreeSum.EncodedColorResources.half n))^(_root_.ThreeSum.EncodedColorResources.blocks n) := Nat.pow_le_pow_left (by omega) _
    _ = 2^(_root_.ThreeSum.EncodedColorResources.blocks n)*localPrime (_root_.ThreeSum.EncodedColorResources.half n)^(_root_.ThreeSum.EncodedColorResources.blocks n) := mul_pow _ _ _
    _ ≤ scale n*scale n := Nat.mul_le_mul (powers n).2.2.2 hmod
    _ = _ := by ring






























theorem keyBound_le (n : ℕ) : LightGuardedWanted.keyBound (maxMod n) (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum.EncodedColorResources.blocks n) ≤ 3*(scale n)^4 := by
  have hP := (scale_bounds n).2.2.2.2.1
  have hL : 512*_root_.ThreeSum.EncodedColorResources.half n ≤ scale n := by have h := (local_bounds n).width; omega
  have hp : localPrime (_root_.ThreeSum.EncodedColorResources.half n) ≤ scale n := by have h := (local_bounds n).prime; omega
  have hm := Nat.mul_le_mul (Nat.mul_le_mul hL hp) (radix_power_le n)
  have hs4 : scale n ≤ (scale n)^4 := Nat.le_self_pow (by decide) _
  unfold LightGuardedWanted.keyBound
  nlinarith only [hm,hP,hs4]

noncomputable section

theorem localEnvelope_powerBound : PowerBound localEnvelope 0 := by
  refine ArithmeticStageBounds.powerBound_mono (g := localSearch 5000000) ?_ ?_
  · intro d hd
    simpa only [zero_add] using localSearch_subpolynomial 5000000 hd
  · filter_upwards [(microHalf_tendsto_atTop.comp inputBits_tendsto_atTop).eventually
      (eventually_ge_atTop 1)] with n hn
    exact LightLocalCoverInitResources.envelope_le_search hn

theorem scale_powerBound : PowerBound scale 2048 := by
  have hl := localEnvelope_powerBound.mono_exponent (by norm_num : (0 : ℝ) ≤ 2048)
  have hp := maxMod_powerBound.mono_exponent (show (Parameters.E+1/2)/5 ≤ (2048 : ℝ) by
    have hh := Parameters.E_bounds.2; linarith)
  have hy := window_powerBound.mono_exponent (by norm_num : (0 : ℝ) ≤ 2048)
  have hn := identity_powerBound.mono_exponent (by norm_num : (1 : ℝ) ≤ 2048)
  have hc := (PowerBound.const 100).mono_exponent (by norm_num : (0 : ℝ) ≤ 2048)
  exact ((((SharedReportingBankResourceBounds.magnitude_powerBound.add_same hl).add_same hp).add_same hy).add_same hn).add_same hc

end
end ThreeSum.EncodedColorResources

end

section


/-!
# Subpolynomial scalar work in the actual selected-color preprocessing

Polynomial resource bounds are used only inside integer logarithms here.
The resulting bit-length work has exponent zero, regardless of the
polynomial degree needed to contain the machine's stored integers.
-/

namespace ThreeSum.EncodedColorTime

open Filter Real Scales BandScales Parameters StageBounds ArithmeticStageBounds
open EncodedColorResources LocalCoverBounds
open scoped Topology

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000

noncomputable section

theorem sum_zero {f g : ℕ → ℕ} (hf : PowerBound f 0) (hg : PowerBound g 0) :
    PowerBound (fun n => f n+g n) 0 := hf.add_same hg

theorem product_zero {f g : ℕ → ℕ} (hf : PowerBound f 0) (hg : PowerBound g 0) :
    PowerBound (fun n => f n*g n) 0 := by simpa only [zero_add] using hf.mul hg

theorem power_zero {f : ℕ → ℕ} (hf : PowerBound f 0) (k : ℕ) :
    PowerBound (fun n => f n^k) 0 := by simpa only [mul_zero] using hf.pow k

theorem log_powerBound {f : ℕ → ℕ} {a : ℝ} (hf : PowerBound f a) :
    PowerBound (fun n => Nat.log 2 (f n+1)) 0 := by
  let k : ℕ := ⌈a+1⌉₊
  have hk : a+1 ≤ (k : ℝ) := Nat.le_ceil _
  apply powerBound_mono (bitBudget_powerBound k)
  filter_upwards [hf 1 (by norm_num),eventually_ge_atTop (1 : ℕ)] with n hn hn1
  have hh := hn.trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn1) hk)
  rw [Real.rpow_natCast] at hh
  have hfn : f n ≤ n^k := by exact_mod_cast hh
  exact (Nat.log_mono_right (b := 2) (Nat.add_le_add_right hfn 1)).trans
    ((Nat.le_succ _).trans (remainder_bits_le k (by omega)))

theorem clog_powerBound {f : ℕ → ℕ} {a : ℝ} (hf : PowerBound f a) :
    PowerBound (fun n => Nat.clog 2 (f n)) 0 := by
  apply powerBound_mono (sum_zero (log_powerBound hf) (PowerBound.const 1))
  exact Eventually.of_forall fun n => Nat.clog_le_of_le_pow
    ((Nat.le_succ (f n)).trans (Nat.lt_pow_succ_log_self (by decide : 1 < 2) (f n+1)).le)

theorem bounded_log {f : ℕ → ℕ} (C e : ℕ)
    (hf : ∀ n, f n ≤ C*(scale n)^e) :
    PowerBound (fun n => Nat.log 2 (f n+1)) 0 :=
  log_powerBound (powerBound_mono ((PowerBound.const C).mul (scale_powerBound.pow e))
    (Eventually.of_forall hf))

theorem half_powerBound : PowerBound _root_.ThreeSum.EncodedColorResources.half 0 := SharedReportingCosts.half_powerBound

theorem blocks_powerBound : PowerBound _root_.ThreeSum.EncodedColorResources.blocks 0 := SharedReportingCosts.blocks_powerBound

theorem local_width_powerBound : PowerBound (fun n => 512*_root_.ThreeSum.EncodedColorResources.half n) 0 :=
  product_zero (PowerBound.const 512) half_powerBound

theorem width_powerBound : PowerBound width 0 :=
  product_zero blocks_powerBound local_width_powerBound

theorem mu_powerBound : PowerBound mu 0 := by
  have hh := product_zero (product_zero (PowerBound.const 2) half_powerBound) blocks_powerBound
  simpa only [_root_.ThreeSum.EncodedColorResources.half,_root_.ThreeSum.EncodedColorResources.blocks,BlockSourceSharing.cutoff_eq] using hh

theorem local_product_log_powerBound :
    PowerBound (fun n => Nat.log 2 ((512*_root_.ThreeSum.EncodedColorResources.half n)*localPrime (_root_.ThreeSum.EncodedColorResources.half n)+1)) 0 := by
  apply bounded_log 1 2
  intro n
  have hL : 512*_root_.ThreeSum.EncodedColorResources.half n ≤ scale n := by have h := (local_bounds n).width; omega
  have hP : localPrime (_root_.ThreeSum.EncodedColorResources.half n) ≤ scale n := by have h := (local_bounds n).prime; omega
  simpa only [one_mul,pow_two] using Nat.mul_le_mul hL hP

theorem endpoint_log_powerBound :
    PowerBound (fun n => Nat.log 2 (LightBlockSourceBuild.endpointBound (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum.EncodedColorResources.blocks n)+1)) 0 :=
  bounded_log 1 2 (fun n => by simpa only [one_mul] using endpoint_le n)

theorem occurrence_log_powerBound :
    PowerBound (fun n => Nat.log 2 (LightBlockSourceCatalog.count (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum.EncodedColorResources.blocks n)+1)) 0 :=
  bounded_log 1 1 (fun n => by simpa only [one_mul,pow_one] using (powers n).2.1)

theorem key_log_powerBound :
    PowerBound (fun n => Nat.log 2 (LightGuardedWanted.keyBound (maxMod n) (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum.EncodedColorResources.blocks n)+1)) 0 :=
  bounded_log 3 4 keyBound_le

theorem moduli_log_powerBound :
    PowerBound (fun n => Nat.log 2 (maxMod n+radix n+1)) 0 := by
  apply bounded_log 2 1
  intro n
  have hp := (scale_bounds n).2.2.2.2.1
  have hm := (dimensions n).2.2.2.2
  simp only [pow_one]
  omega

theorem radix_log_powerBound :
    PowerBound (fun n => Nat.log 2 (radix n+radix n+1)) 0 := by
  apply bounded_log 2 1
  intro n
  have hm := (dimensions n).2.2.2.2
  simp only [pow_one]
  omega

theorem input_log_powerBound (k : ℕ) : PowerBound (fun n => Nat.log 2 (n^k+1)) 0 :=
  log_powerBound (identity_powerBound.pow k)

end
end ThreeSum.EncodedColorTime

end

section


/-! # Running time of the executed occurrence-shared source banks -/

namespace ThreeSum.EncodedColorTime

open Filter Real Scales BandScales Parameters StageBounds ArithmeticStageBounds
open EncodedColorResources CostLedger

set_option maxHeartbeats 1800000
set_option maxRecDepth 12000

noncomputable section

theorem retained_factor_powerBound :
    PowerBound (fun n => LightBlockSourceRetainedProgram.factor (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum.EncodedColorResources.blocks n)) 0 := by
  have hw := sum_zero width_powerBound (PowerBound.const 1)
  have hj := sum_zero blocks_powerBound (PowerBound.const 1)
  have hl := sum_zero local_width_powerBound (PowerBound.const 1)
  have hp := sum_zero local_product_log_powerBound (PowerBound.const 1)
  have he := sum_zero endpoint_log_powerBound (PowerBound.const 1)
  have h1 := product_zero (PowerBound.const 1200) (power_zero hw 2)
  have h2 := product_zero (product_zero (PowerBound.const 300) hj) hl
  have h3 := product_zero (PowerBound.const 600) hw
  have h4a := product_zero (PowerBound.const 300) (power_zero hw 2)
  have h4b := sum_zero (sum_zero (product_zero (PowerBound.const 150) local_width_powerBound)
    (product_zero (PowerBound.const 464) hp)) (PowerBound.const 250)
  have h4 := sum_zero (sum_zero h4a (product_zero blocks_powerBound h4b)) (PowerBound.const 400)
  have h5 := product_zero (PowerBound.const 314) he
  have h6 := product_zero (PowerBound.const 12000) (power_zero hw 4)
  simpa only [LightBlockSourceRetainedProgram.factor,width] using
    sum_zero (sum_zero (sum_zero (sum_zero (sum_zero (sum_zero h1 h2) h3) h4) h5) h6)
      (PowerBound.const 1122)

theorem catalog_factor_powerBound :
    PowerBound (fun n => LightBlockSourceCatalogProgram.factor (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum.EncodedColorResources.blocks n)) 0 := by
  have hj := sum_zero blocks_powerBound (PowerBound.const 1)
  have hr := sum_zero occurrence_log_powerBound (PowerBound.const 2)
  exact sum_zero (sum_zero retained_factor_powerBound (PowerBound.const 1120))
    (product_zero (product_zero (PowerBound.const 300) hj) hr)

theorem controls_factor_powerBound :
    PowerBound (fun n => SourceControlCosts.factor (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum.EncodedColorResources.blocks n)) 0 := by
  have hw := sum_zero width_powerBound (PowerBound.const 1)
  have h1 := product_zero (PowerBound.const 1400) (power_zero hw 2)
  have h2 := product_zero (PowerBound.const 20) blocks_powerBound
  have h3 := product_zero (PowerBound.const 14) local_product_log_powerBound
  have h4 := product_zero (PowerBound.const 14) endpoint_log_powerBound
  simpa only [SourceControlCosts.factor,width] using
    sum_zero (sum_zero (sum_zero (sum_zero h1 h2) h3) h4) (PowerBound.const 2044)

theorem source_factor_powerBound (k : ℕ) :
    PowerBound (fun n =>
      LightBlockSourceCatalogProgram.factor (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum.EncodedColorResources.blocks n)*(256*mu n+2)+
        2032*(Nat.log 2 (n^k+1)+Nat.log 2 (maxMod n+radix n+1)+1)+
        SourceControlCosts.factor (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum.EncodedColorResources.blocks n)+5705) 0 := by
  have hc := sum_zero (product_zero (PowerBound.const 256) mu_powerBound) (PowerBound.const 2)
  have hb := sum_zero (sum_zero (input_log_powerBound k) moduli_log_powerBound) (PowerBound.const 1)
  exact sum_zero (sum_zero (sum_zero (product_zero catalog_factor_powerBound hc)
    (product_zero (PowerBound.const 2032) hb)) controls_factor_powerBound) (PowerBound.const 5705)

theorem source_time_powerBound (k : ℕ) :
    PowerBound (fun n => SourceFiniteCosts.time n (maxMod n) (n^k) (radix n))
      (1+epsilon*(E-bandShift)) := by
  have he : (0 : ℝ) ≤ 1+epsilon*(E-bandShift) := by
    have h := E_bounds.1
    unfold epsilon bandShift
    linarith
  have hh := (source_factor_powerBound k).mul encoder_powerBound
  simp only [zero_add] at hh
  exact hh.add_same ((PowerBound.const 4859).mono_exponent he)

theorem sources_time_powerBound (k : ℕ) :
    PowerBound (fun n => EncodedColorSourcesCosts.time n (maxMod n) (n^k) (radix n))
      (1+epsilon*(E-bandShift)) := by
  have he : (0 : ℝ) ≤ 1+epsilon*(E-bandShift) := by
    have h := E_bounds.1
    unfold epsilon bandShift
    linarith
  have hJ := (product_zero (PowerBound.const 20) blocks_powerBound).mono_exponent he
  have hh := ((source_time_powerBound k).add_same hJ).add_same
    ((PowerBound.const 1020).mono_exponent he)
  simpa only [EncodedColorSourcesCosts.time_eq,_root_.ThreeSum.EncodedColorResources.blocks] using hh

theorem sources_time_certificate (k : ℕ) :
    PowerBound (fun n => EncodedColorSourcesCosts.time n (maxMod n) (n^k) (radix n))
      certificateExponent :=
  (sources_time_powerBound k).mono_exponent (all_costs_le_certificate _ (by simp [costLedger]))

end
end ThreeSum.EncodedColorTime

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

theorem total_keys_eq (n : ℕ) :
    LightGuardedWanted.totalKeys (microHalf (inputBits n)) (blockCount (inputBits n))=
      TrimScales.scheduleCount n*typedOutputs n := by
  have hh : 2*microHalf (inputBits n)=muZero n := rfl
  have hw : 512*microHalf (inputBits n)=256*muZero n := by rw [← hh]; ring
  unfold LightGuardedWanted.totalKeys LightGlobalKeys.localCount outputCount
    TrimScales.scheduleCount TrimScales.replicatedHalf TrimScales.localLength typedOutputs
  rw [mul_pow,scheduleSize_eq_length]
  congr 1
  rw [hh,hw]







variable {μ : ℕ → ℤ} {free n : ℕ}
    {color : Coloring.Parameter (inputBits n+1)} {x : Fin n → ℤ}
    {A B C : List ℤ} {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
































































































open Filter













end ThreeSum.ThreeSumColorBudgets

end

section


/-! # Exact physical count scales for the selected-color preprocessing -/

namespace ThreeSum.EncodedColorTime

open Filter Real Scales BandScales Parameters StageBounds ArithmeticStageBounds
open EncodedColorResources CostLedger HierarchyScales

set_option maxHeartbeats 1600000
set_option maxRecDepth 12000

noncomputable section

theorem band_powerBound : PowerBound bandSize ((E+bandShift)/5) :=
  PowerBound.of_rate MassScales.bandSize_log_rate_shift

theorem count_powerBound :
    PowerBound (fun n => ColorBandBounds.count n (bandSize n)) (2*(1-(E+bandShift)/5)) := by
  apply powerBound_mono BandPrimeCosts.owner_count_powerBound
  exact Eventually.of_forall fun n => by
    have hs := SourceBandCosts.size_le_bandCount (n := n) (le_refl n)
    have hh := Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left hs 2)
    exact hh.trans (Nat.le_succ _)

theorem incidence_powerBound :
    PowerBound EncodedColorStageCosts.incidenceCap (2-(E+bandShift)/5) := by
  have hh := band_powerBound.mul count_powerBound
  convert hh using 1 <;> (first | rfl | ring)

theorem keys_powerBound :
    PowerBound (fun n => LightGuardedWanted.totalKeys (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum.EncodedColorResources.blocks n)) (2*epsilon*E) := by
  have hh := (PowerBound.of_rate TrimScales.scheduleCount_log_rate).mul
    (PowerBound.of_rate typedOutputs_log_ratio_tendsto)
  have he : (0 : ℝ)+2*E/5=2*epsilon*E := by unfold epsilon; ring
  rw [he] at hh
  simpa only [_root_.ThreeSum.EncodedColorResources.half,_root_.ThreeSum.EncodedColorResources.blocks,ThreeSumColorBudgets.total_keys_eq] using hh

theorem wanted_rows_le (n : ℕ) :
    3*EncodedColorStageCosts.incidenceCap n*LightGuardedWanted.totalKeys (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum.EncodedColorResources.blocks n)/radix n ≤
      UniformStageBounds.wantedBudget n := by
  have hs := SourceBandCosts.size_le_bandCount (n := n) (le_refl n)
  have hcap : EncodedColorStageCosts.incidenceCap n ≤ bandSize n*(3*bandCount n^2) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left hs 2))
  have hc := Nat.mul_le_mul_right (LightGuardedWanted.totalKeys (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum.EncodedColorResources.blocks n))
    (Nat.mul_le_mul_left 3 hcap)
  have he : 3*(bandSize n*(3*bandCount n^2))*LightGuardedWanted.totalKeys (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum.EncodedColorResources.blocks n)=
      MassScales.wantedNumerator n := by
    rw [show LightGuardedWanted.totalKeys (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum.EncodedColorResources.blocks n)=
      TrimScales.scheduleCount n*typedOutputs n from ThreeSumColorBudgets.total_keys_eq n]
    unfold MassScales.wantedNumerator
    ring
  rw [he] at hc
  exact Nat.div_le_div_right hc

theorem wanted_rows_powerBound :
    PowerBound (fun n =>
      3*EncodedColorStageCosts.incidenceCap n*LightGuardedWanted.totalKeys (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum.EncodedColorResources.blocks n)/radix n)
      (2-(1/2+bandShift)/5) :=
  powerBound_mono UniformStageBounds.wantedBudget_powerBound (Eventually.of_forall wanted_rows_le)

theorem incidence_three_halves : PowerBound EncodedColorStageCosts.incidenceCap (3/2) :=
  incidence_powerBound.mono_exponent (by have h := E_bounds.1; unfold bandShift; linarith)

theorem count_one : PowerBound (fun n => ColorBandBounds.count n (bandSize n)) 1 :=
  count_powerBound.mono_exponent (by have h := E_bounds.1; unfold bandShift; linarith)

theorem keys_certificate :
    PowerBound (fun n => LightGuardedWanted.totalKeys (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum.EncodedColorResources.blocks n)) certificateExponent :=
  keys_powerBound.mono_exponent (all_costs_le_certificate _ (by simp [costLedger]))

theorem incidence_certificate : PowerBound EncodedColorStageCosts.incidenceCap certificateExponent :=
  incidence_three_halves.mono_exponent (by norm_num [certificateExponent])

theorem radix_certificate : PowerBound radix certificateExponent :=
  (PowerBound.of_rate radix_log_ratio_tendsto).mono_exponent (by
    have h := E_bounds.2
    unfold certificateExponent
    linarith)

theorem wanted_rows_certificate :
    PowerBound (fun n =>
      3*EncodedColorStageCosts.incidenceCap n*LightGuardedWanted.totalKeys (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum.EncodedColorResources.blocks n)/radix n)
      certificateExponent :=
  wanted_rows_powerBound.mono_exponent (by norm_num [bandShift,certificateExponent])

end
end ThreeSum.EncodedColorTime

end

section


/-! # Time of the actual color extraction, normalization and incidence catalog -/

namespace ThreeSum.EncodedColorTime

open Filter Real Scales BandScales Parameters StageBounds ArithmeticStageBounds
open EncodedColorResources CostLedger HierarchyScales

set_option maxHeartbeats 1800000
set_option maxRecDepth 12000

noncomputable section

theorem band_width_powerBound :
    PowerBound (fun n => ColorBandBounds.width n (bandSize n)) 0 := by
  have hs : PowerBound (fun n => BandPartition.size n (bandSize n)) 1 :=
    powerBound_mono identity_powerBound (Eventually.of_forall fun n => BandPartition.size_le n _)
  exact clog_powerBound (((hs.add_same hs).add_same hs).add_same
    ((PowerBound.const 1).mono_exponent (by norm_num : (0 : ℝ) ≤ 1)))

theorem band_time_powerBound :
    PowerBound (fun n => ColorBandBounds.time n (bandSize n)) 1 := by
  have hn := identity_powerBound.add_same ((PowerBound.const 1).mono_exponent (by norm_num : (0 : ℝ) ≤ 1))
  have hl := sum_zero (clog_powerBound identity_powerBound) (PowerBound.const 1)
  have hw := sum_zero band_width_powerBound (PowerBound.const 1)
  have hR := (count_one.add_same identity_powerBound).add_same
    ((PowerBound.const 1).mono_exponent (by norm_num : (0 : ℝ) ≤ 1))
  have h1 : PowerBound (fun n => 2100*(n+1)*(Nat.clog 2 n+1)) 1 := by
    simpa only [zero_add,add_zero] using ((PowerBound.const 2100).mul hn).mul hl
  have h2 : PowerBound (fun n => 1000*(ColorBandBounds.count n (bandSize n)+n+1)*
      (ColorBandBounds.width n (bandSize n)+1)) 1 := by
    simpa only [zero_add,add_zero] using ((PowerBound.const 1000).mul hR).mul hw
  exact (h1.add_same h2).add_same ((PowerBound.const 400).mono_exponent (by norm_num : (0 : ℝ) ≤ 1))

theorem raw_catalog_time_le (n : ℕ) :
    LightBandRawAColor.catalogTime n (bandSize n) ≤ 9000*(3*bandCount n^2+1)*(bandSize n+1) := by
  have hs := SourceBandCosts.size_le_bandCount (n := n) (le_refl n)
  have hc := Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left hs 2)
  have hb : bandCount n ≤ bandCount n^2 := Nat.le_self_pow (by decide) _
  have hsum : ColorBandBounds.count n (bandSize n)+3*BandPartition.size n (bandSize n)+1 ≤
      3*(3*bandCount n^2+1) := by
    unfold ColorBandBounds.count
    omega
  have hh := Nat.mul_le_mul_right (bandSize n+1) (Nat.mul_le_mul_left 3000 hsum)
  have he : 3000*(3*(3*bandCount n^2+1))=9000*(3*bandCount n^2+1) := by omega
  rw [he] at hh
  exact hh

theorem raw_catalog_time_powerBound :
    PowerBound (fun n => LightBandRawAColor.catalogTime n (bandSize n)) (2-(E+bandShift)/5) := by
  have he : (0 : ℝ) ≤ (E+bandShift)/5 := by
    have h := E_bounds.1
    unfold bandShift
    linarith
  have hg := band_powerBound.add_same ((PowerBound.const 1).mono_exponent he)
  have hh := ((PowerBound.const 9000).mul BandPrimeCosts.owner_count_powerBound).mul hg
  have heq : (0 : ℝ)+2*(1-(E+bandShift)/5)+(E+bandShift)/5=2-(E+bandShift)/5 := by ring
  rw [heq] at hh
  exact powerBound_mono hh (Eventually.of_forall raw_catalog_time_le)

theorem color_bands_time_powerBound :
    PowerBound (fun n => LightBandRawAColor.time (inputBits n+1) n (bandSize n)) (3/2) := by
  have hb := sum_zero (sum_zero SharedReportingCosts.bits_powerBound (PowerBound.const 1))
    (PowerBound.const 1)
  have hn := identity_powerBound.add_same ((PowerBound.const 1).mono_exponent (by norm_num : (0 : ℝ) ≤ 1))
  have hlin : PowerBound (fun n => 1200*(inputBits n+1+1)*(n+1)) 1 := by
    simpa only [zero_add] using ((PowerBound.const 1200).mul hb).mul hn
  have h1 := hlin.mono_exponent (by norm_num : (1 : ℝ) ≤ 3/2)
  have h2 := band_time_powerBound.mono_exponent (by norm_num : (1 : ℝ) ≤ 3/2)
  have h3 := raw_catalog_time_powerBound.mono_exponent (show 2-(E+bandShift)/5 ≤ (3/2 : ℝ) by
    have h := E_bounds.1; unfold bandShift; linarith)
  have h4 := (PowerBound.const 600).mono_exponent (by norm_num : (0 : ℝ) ≤ 3/2)
  exact powerBound_mono (((h1.add_same h2).add_same h3).add_same h4)
    (Eventually.of_forall fun n => LightBandRawAColor.time_bound (inputBits n+1) n (bandSize n))

theorem normalized_layout_time_powerBound :
    PowerBound (fun n => LightEncodedColorLayout.time n (bandSize n)) 1 := by
  have hh : PowerBound (fun n => 20*n+1040) 1 := by
    have h := (PowerBound.const 20).mul identity_powerBound
    simp only [zero_add] at h
    exact h.add_same ((PowerBound.const 1040).mono_exponent (by norm_num : (0 : ℝ) ≤ 1))
  apply powerBound_mono hh
  exact Eventually.of_forall fun n => by
    have h := LightSmallDivide.time_bound (n-1) (bandSize n)
    unfold LightEncodedColorLayout.time
    omega

theorem normalize_time_powerBound : PowerBound LightEncodedColorNormalize.time (3/2) :=
  (((normalized_layout_time_powerBound.mono_exponent (by norm_num : (1 : ℝ) ≤ 3/2)).add_same
    color_bands_time_powerBound).add_same
      ((PowerBound.const 1200).mono_exponent (by norm_num : (0 : ℝ) ≤ 3/2)))

theorem normalize_time_certificate : PowerBound LightEncodedColorNormalize.time certificateExponent :=
  normalize_time_powerBound.mono_exponent (by norm_num [certificateExponent])

end
end ThreeSum.EncodedColorTime

end

section


/-! # Time of constructing the retained local cover and all global key rows -/

namespace ThreeSum.EncodedColorTime

open Filter Real Scales BandScales Parameters StageBounds ArithmeticStageBounds
open EncodedColorResources CostLedger LocalCoverBounds GlobalEncoding

set_option maxHeartbeats 1600000
set_option maxRecDepth 12000

theorem local_magnitude_le (n : ℕ) :
    LightLocalCoverMagnitude.magnitude (_root_.ThreeSum.EncodedColorResources.half n) ≤ localEnvelope n := by
  unfold LightLocalCoverMagnitude.magnitude localEnvelope LightLocalCoverInitResources.envelope
  exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (by decide : 600000 ≤ 5000000))

noncomputable section

theorem local_schedule_powerBound : PowerBound (fun n => scheduleSize (_root_.ThreeSum.EncodedColorResources.half n)) 0 := by
  apply powerBound_mono localEnvelope_powerBound
  exact Eventually.of_forall fun n => by
    have h := (LightLocalCoverMagnitude.bounds (_root_.ThreeSum.EncodedColorResources.half n)).rounds.trans (local_magnitude_le n)
    omega

theorem local_layer_powerBound : PowerBound (fun n => outputCount (512*_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum.EncodedColorResources.half n)) 0 := by
  apply powerBound_mono localEnvelope_powerBound
  exact Eventually.of_forall fun n => by
    have h := (LightLocalCoverMagnitude.bounds (_root_.ThreeSum.EncodedColorResources.half n)).maskPower.trans (local_magnitude_le n)
    have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (Nat.le_succ (512*_root_.ThreeSum.EncodedColorResources.half n))
    exact (Nat.choose_le_two_pow _ _).trans (hp.trans (by omega))

theorem local_cover_time_powerBound : PowerBound (fun n => LightLocalCoverInit.time (_root_.ThreeSum.EncodedColorResources.half n)) 0 :=
  powerBound_mono localEnvelope_powerBound (Eventually.of_forall fun n =>
    LightLocalCoverInitResources.time_bound (_root_.ThreeSum.EncodedColorResources.half n))

theorem global_keys_time_powerBound :
    PowerBound (fun n => LightGlobalKeys.time (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum.EncodedColorResources.blocks n)) (2*epsilon*E) := by
  have he : (0 : ℝ) ≤ 2*epsilon*E := by
    have h := E_bounds.1
    unfold epsilon
    linarith
  have hl := sum_zero local_width_powerBound (PowerBound.const 1)
  have hq := sum_zero local_layer_powerBound (PowerBound.const 1)
  have hs := sum_zero local_schedule_powerBound (PowerBound.const 1)
  have hlocal := product_zero (product_zero (product_zero (PowerBound.const 2000) hl) hq) hs
  have hj := sum_zero blocks_powerBound (PowerBound.const 1)
  have hg := keys_powerBound.add_same ((PowerBound.const 1).mono_exponent he)
  have hglobal : PowerBound (fun n => 300*(_root_.ThreeSum.EncodedColorResources.blocks n+1)*
      (LightGlobalKeys.localCount (_root_.ThreeSum.EncodedColorResources.half n)^(_root_.ThreeSum.EncodedColorResources.blocks n)+1)) (2*epsilon*E) := by
    simpa only [zero_add,LightGuardedWanted.totalKeys] using (product_zero (PowerBound.const 300) hj).mul hg
  exact powerBound_mono (((hlocal.mono_exponent he).add_same hglobal).add_same
    ((PowerBound.const 200).mono_exponent he))
    (Eventually.of_forall fun n => LightGlobalKeys.time_bound (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum.EncodedColorResources.blocks n))

theorem cover_time_powerBound :
    PowerBound (fun n => LightCoverKeys.time (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum.EncodedColorResources.blocks n)) (2*epsilon*E) := by
  have he : (0 : ℝ) ≤ 2*epsilon*E := by
    have h := E_bounds.1
    unfold epsilon
    linarith
  exact ((local_cover_time_powerBound.mono_exponent he).add_same global_keys_time_powerBound).add_same
    ((PowerBound.const 200).mono_exponent he)

theorem cover_time_certificate :
    PowerBound (fun n => LightCoverKeys.time (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum.EncodedColorResources.blocks n)) certificateExponent :=
  cover_time_powerBound.mono_exponent (all_costs_le_certificate _ (by simp [costLedger]))

end
end ThreeSum.EncodedColorTime

end

section


/-!
# Time of the actual balanced wanted-record construction

The emitted-record term retains the proved division by the dense modulus.
The remaining terms scan the original A incidences and global key rows,
construct histograms, and execute the verified correlation/minimum routine.
-/

namespace ThreeSum.EncodedColorTime

open Filter Real Scales BandScales Parameters StageBounds ArithmeticStageBounds
open EncodedColorResources CostLedger ModuloCosts

set_option maxHeartbeats 1800000
set_option maxRecDepth 14000

theorem original_offset_time_le (p NL NR U : ℕ) :
    LightOriginalOffset.time p NL NR U ≤
      3000*roundedPower p+131*(NL+NR)*(Nat.log 2 (U+1)+1)+642 := by
  have ht := LightOriginalOffset.time_bound p NL NR U
  have hc := capacity_le_roundedPower p
  have hl := log_le_roundedPower p
  have hk : LightKaratsuba.time (Nat.clog 2 p) ≤ 2530*roundedPower p := LightKaratsuba.time_le _
  omega

noncomputable section

theorem const_certificate (c : ℕ) : PowerBound (fun _ => c) certificateExponent :=
  (PowerBound.const c).mono_exponent (by norm_num [certificateExponent])

theorem raw_keys_time_powerBound (k : ℕ) :
    PowerBound (fun n => LightRawAKeys.time (EncodedColorStageCosts.incidenceCap n) (n^k)) (3/2) := by
  have hc := incidence_three_halves.add_same
    ((PowerBound.const 1).mono_exponent (by norm_num : (0 : ℝ) ≤ 3/2))
  have hl := sum_zero (input_log_powerBound k) (PowerBound.const 1)
  have hh : PowerBound (fun n => 220*(EncodedColorStageCosts.incidenceCap n+1)*
      (Nat.log 2 (n^k+1)+1)) (3/2) := by
    simpa only [zero_add,add_zero] using ((PowerBound.const 220).mul hc).mul hl
  exact powerBound_mono hh (Eventually.of_forall fun n => LightRawAKeys.time_bound _ _)

theorem rounded_radix_powerBound :
    PowerBound (fun n => roundedPower (radix n)) ((8/5)*((E+1/2)/5)) := by
  apply powerBound_of_fifth (PowerBound.of_rate radix_log_ratio_tendsto)
  intro n
  simpa only [show (2 : ℕ)^8=256 by norm_num] using roundedPower_fifth (radix_pos n)

theorem rounded_radix_certificate :
    PowerBound (fun n => roundedPower (radix n)) certificateExponent :=
  rounded_radix_powerBound.mono_exponent (by
    have h := E_bounds.2
    unfold certificateExponent
    linarith)

theorem left_keys_certificate :
    PowerBound (fun n => 3*EncodedColorStageCosts.incidenceCap n) certificateExponent := by
  simpa only [zero_add] using (PowerBound.const 3).mul incidence_certificate

theorem original_offset_time_certificate :
    PowerBound (fun n => LightOriginalOffset.time (radix n) (3*EncodedColorStageCosts.incidenceCap n)
      (LightGuardedWanted.totalKeys (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum.EncodedColorResources.blocks n))
      (LightGuardedWanted.keyBound (maxMod n) (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum.EncodedColorResources.blocks n))) certificateExponent := by
  have hcount := left_keys_certificate.add_same keys_certificate
  have hlog := sum_zero key_log_powerBound (PowerBound.const 1)
  have h1 : PowerBound (fun n => 3000*roundedPower (radix n)) certificateExponent := by
    simpa only [zero_add] using (PowerBound.const 3000).mul rounded_radix_certificate
  have h2 : PowerBound (fun n => 131*(3*EncodedColorStageCosts.incidenceCap n+
      LightGuardedWanted.totalKeys (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum.EncodedColorResources.blocks n))*
      (Nat.log 2 (LightGuardedWanted.keyBound (maxMod n) (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum.EncodedColorResources.blocks n)+1)+1))
      certificateExponent := by
    simpa only [zero_add,add_zero] using ((PowerBound.const 131).mul hcount).mul hlog
  exact powerBound_mono ((h1.add_same h2).add_same (const_certificate 642))
    (Eventually.of_forall fun n => original_offset_time_le _ _ _ _)

theorem wanted_scan_time_certificate :
    PowerBound (fun n =>
      2000*(3*EncodedColorStageCosts.incidenceCap n+LightGuardedWanted.totalKeys (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum.EncodedColorResources.blocks n)+
        radix n+3*EncodedColorStageCosts.incidenceCap n*
          LightGuardedWanted.totalKeys (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum.EncodedColorResources.blocks n)/radix n+1)*
        (Nat.log 2 (LightGuardedWanted.keyBound (maxMod n) (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum.EncodedColorResources.blocks n)+1)+
          Nat.log 2 (radix n+radix n+1)+1)) certificateExponent := by
  have hc := (((left_keys_certificate.add_same keys_certificate).add_same radix_certificate).add_same
    wanted_rows_certificate).add_same (const_certificate 1)
  have hl := sum_zero (sum_zero key_log_powerBound radix_log_powerBound) (PowerBound.const 1)
  simpa only [zero_add,add_zero] using ((PowerBound.const 2000).mul hc).mul hl

theorem wanted_time_certificate (k : ℕ) :
    PowerBound (fun n => EncodedColorWantedCosts.time (maxMod n) (radix n) (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum.EncodedColorResources.blocks n)
      (n^k) (EncodedColorStageCosts.incidenceCap n)) certificateExponent := by
  have hraw := (raw_keys_time_powerBound k).mono_exponent
    (show (3/2 : ℝ) ≤ certificateExponent by norm_num [certificateExponent])
  exact (((cover_time_certificate.add_same hraw).add_same original_offset_time_certificate).add_same
    wanted_scan_time_certificate).add_same (const_certificate 400)

end
end ThreeSum.EncodedColorTime

end

section


/-!
# The executed selected-color preprocessing fits the final time exponent

This charges the actual fixed256 program's complete time expression:
normalization and incidence construction, common-prime selection, local
cover and global keys, balanced wanted rows, shared source banks and the
retained result-header computation. Reporting and the outer color loop
remain separate composition obligations.
-/

namespace ThreeSum.EncodedColorTime

open Filter Real Scales BandScales Parameters StageBounds ArithmeticStageBounds
open EncodedColorResources CostLedger
open scoped Topology

set_option maxHeartbeats 1800000
set_option maxRecDepth 12000



noncomputable section

theorem prime_time_certificate (k : ℕ) :
    PowerBound (fun n => LightEncodedColorPrime.time (maxMod n) n n n (bandSize n)
      (radix n) (primeWindow n) (n^k)) certificateExponent := by
  apply powerBound_mono ((BandPrimeCosts.timeBudget_certificate k).add_same (const_certificate 1160))
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  exact EncodedColorPrimeCosts.time_le_budget (nA := n) (nB := n) (nC := n)
    (n := n) k (by omega) le_rfl le_rfl le_rfl

theorem prime_host_time_certificate (k : ℕ) :
    PowerBound (fun n => LightEncodedColorPrimeHost.inputTime n (n^k)) certificateExponent := by
  change PowerBound (fun n => LightEncodedColorNormalize.time n+
    LightEncodedColorPrime.time (maxMod n) n n n (bandSize n) (radix n) (primeWindow n) (n^k)+600) _
  exact (normalize_time_certificate.add_same (prime_time_certificate k)).add_same (const_certificate 600)

theorem stage_time_certificate (k : ℕ) :
    PowerBound (fun n => EncodedColorStageCosts.time n (maxMod n) (radix n) (n^k)
      (EncodedColorStageCosts.incidenceCap n)) certificateExponent := by
  change PowerBound (fun n => EncodedColorWantedCosts.time (maxMod n) (radix n) (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum.EncodedColorResources.blocks n)
    (n^k) (EncodedColorStageCosts.incidenceCap n)+EncodedColorSourcesCosts.time n (maxMod n) (n^k) (radix n)+400) _
  exact ((wanted_time_certificate k).add_same (sources_time_certificate k)).add_same (const_certificate 400)

theorem wanted_header_time_powerBound :
    PowerBound (fun n => LightEncodedColorWantedHeader.time (_root_.ThreeSum.EncodedColorResources.blocks n)) 0 :=
  sum_zero (product_zero (PowerBound.const 100) blocks_powerBound) (PowerBound.const 1000)

theorem pipeline_time_powerBound (k : ℕ) : PowerBound (preprocessingTime k) certificateExponent := by
  change PowerBound (fun n => LightEncodedColorPrimeHost.inputTime n (n^k)+
    EncodedColorStageCosts.time n (maxMod n) (radix n) (n^k) (EncodedColorStageCosts.incidenceCap n)+
    LightEncodedColorWantedHeader.time (_root_.ThreeSum.EncodedColorResources.blocks n)+1600) _
  have hh := wanted_header_time_powerBound.mono_exponent (show (0 : ℝ) ≤ certificateExponent by
    norm_num [certificateExponent])
  exact (((prime_host_time_certificate k).add_same (stage_time_certificate k)).add_same hh).add_same
    (const_certificate 1600)












end
end ThreeSum.EncodedColorTime

end

section


/-!
# Charge the actual threshold construction

One final aggregate score is covered by the existing executed arithmetic
budget. Computing the cap and storing its product adds only O(J) work.
This is a cost theorem for this concrete stage, not a full solver claim.
-/

namespace ThreeSum.LightDenseSetupCosts

open Scales BandScales CostLedger ArithmeticStageBounds Parameters

set_option maxHeartbeats 1400000
set_option maxRecDepth 8000

theorem aggregate_time_le_budget {n R : ℕ} (k : ℕ) (hn : 0 < n)
    (hR : R ≤ 3*bandCount n^2) :
    LightBandWeightedScore.time (maxMod n) (bandSize n) R
      (LightPrimePool.size (primeWindow n)) (n^k) ≤ BandPrimeCosts.timeBudget k n := by
  let s := LightPrimePool.size (primeWindow n)
  have hs : s+1 ≤ (s+1)^2 := by nlinarith
  have hd : 6 ≤ 15*(primeDepth radix n+1) := by omega
  have ht := BandPrimeCosts.aggregate_time_le (maxMod n) (bandSize n) R s (n^k)
  have hu := BandPrimeCosts.unit_le_budget k hn
  calc
    _ ≤ 2*(R+1)*(s+1)*BandPrimeCosts.unit (maxMod n) (bandSize n) (n^k) := ht
    _ ≤ 2*(3*bandCount n^2+1)*(s+1)*(3*perTripleBudget k n) := by gcongr
    _ = 6*((3*bandCount n^2+1)*((s+1)*perTripleBudget k n)) := by ring
    _ ≤ (15*(primeDepth radix n+1))*
        ((3*bandCount n^2+1)*((s+1)^2*perTripleBudget k n)) :=
      Nat.mul_le_mul hd (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hs))
    _ ≤ BandPrimeCosts.timeBudget k n := by unfold BandPrimeCosts.timeBudget; dsimp [s]; nlinarith




theorem time_le_budget {n R : ℕ} (k : ℕ) (hn : 0 < n)
    (hR : R ≤ 3*bandCount n^2) :
    LightDenseSetup.time (maxMod n) (bandSize n) R (LightPrimePool.size (primeWindow n))
      (n^k) (blockCount (inputBits n)) ≤ timeBudget k n := by
  have hh := aggregate_time_le_budget k hn hR
  unfold LightDenseSetup.time LightDenseCap.time LightNatPower.time timeBudget
  omega

open Filter Real StageBounds
open scoped Topology

noncomputable section

theorem scalar_time_powerBound : PowerBound (fun n => 20*blockCount (inputBits n)+570) 0 := by
  have hj := (PowerBound.const 20).mul SharedReportingCosts.blocks_powerBound
  have hj' : PowerBound (fun n => 20*blockCount (inputBits n)) 0 := by
    simpa only [zero_add,SharedReportingCosts.blocks] using hj
  exact hj'.add_same (PowerBound.const 570)

theorem timeBudget_powerBound (k : ℕ) :
    PowerBound (timeBudget k) (2+epsilon*(4/5-(2/5)*E-2*bandShift)) := by
  change PowerBound (fun n => BandPrimeCosts.timeBudget k n+20*blockCount (inputBits n)+570)
    (2+epsilon*(4/5-(2/5)*E-2*bandShift))
  have he : (0 : ℝ) ≤ 2+epsilon*(4/5-(2/5)*E-2*bandShift) := by
    have hh := E_bounds.2
    unfold epsilon bandShift
    linarith
  have hh := (BandPrimeCosts.timeBudget_powerBound k).add_same (scalar_time_powerBound.mono_exponent he)
  simpa only [Nat.add_assoc] using hh

theorem timeBudget_certificate (k : ℕ) : PowerBound (timeBudget k) certificateExponent :=
  (timeBudget_powerBound k).mono_exponent (all_costs_le_certificate _ (by simp [costLedger]))








end
end ThreeSum.LightDenseSetupCosts

end

section


/-! # Actual time of the source, shared reporting and dense prelude -/

namespace ThreeSum.EncodedColorReportingCosts

open Filter Real Scales BandScales Parameters StageBounds ArithmeticStageBounds
open CostLedger
open scoped Topology

set_option maxHeartbeats 1800000
set_option maxRecDepth 12000














theorem dense_time_le_budget {n : ℕ} (k : ℕ) (hn : 0 < n) :
    LightThreeSumReportingSetupDense.time n (n^k) (ColorBandBounds.count n (bandSize n)) ≤
      LightDenseSetupCosts.timeBudget k n+1600 := by
  have hs := SourceBandCosts.size_le_bandCount (n := n) (le_refl n)
  have hc : ColorBandBounds.count n (bandSize n) ≤ 3*bandCount n^2 :=
    Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left hs 2)
  exact Nat.add_le_add_right (LightDenseSetupCosts.time_le_budget k hn hc) 1600

noncomputable section

theorem bank_time_certificate :
    PowerBound LightThreeSumReportingSetupBank.time certificateExponent := by
  change PowerBound (fun n => SharedReportingBankCosts.budget n+400) _
  exact SharedReportingBankCosts.budget_certificate.add_same (EncodedColorTime.const_certificate 400)

theorem dense_time_certificate (k : ℕ) :
    PowerBound (fun n => LightThreeSumReportingSetupDense.time n (n^k)
      (ColorBandBounds.count n (bandSize n))) certificateExponent := by
  apply powerBound_mono ((LightDenseSetupCosts.timeBudget_certificate k).add_same
    (EncodedColorTime.const_certificate 1600))
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  exact dense_time_le_budget k (by omega)

theorem setup_time_certificate (k : ℕ) :
    PowerBound (fun n => setupTime n (n^k)) certificateExponent := by
  change PowerBound (fun n => LightThreeSumReportingSetupBank.time n+
    LightThreeSumReportingSetupDense.time n (n^k) (ColorBandBounds.count n (bandSize n))+200) _
  exact (bank_time_certificate.add_same (dense_time_certificate k)).add_same
    (EncodedColorTime.const_certificate 200)

theorem time_powerBound (k : ℕ) : PowerBound (preprocessingTime k) certificateExponent := by
  change PowerBound (fun n => EncodedColorTime.preprocessingTime k n+setupTime n (n^k)+1000) _
  exact ((EncodedColorTime.pipeline_time_powerBound k).add_same (setup_time_certificate k)).add_same
    (EncodedColorTime.const_certificate 1000)












end
end ThreeSum.EncodedColorReportingCosts

end

section


/-! # Exact polynomial resources for the executed parameter initializer

The nineteen-cell output starts at an arbitrary destination. Scratch begins
immediately after that header; its reservation is translated only once.
-/

namespace ThreeSum.ThreeSumParameterResources

open Light Scales BandScales LocalCoverBounds EncodedColorResources StageBounds

set_option maxHeartbeats 2200000
set_option maxRecDepth 14000







theorem local_envelope_le (n : ℕ) :
    LocalParameterBounds.envelope (LightParameterInit.half n) ≤ localEnvelope n := by
  unfold LocalParameterBounds.envelope localEnvelope LightLocalCoverInitResources.envelope
  apply Nat.pow_le_pow_right (by decide)
  change 2048*(_root_.ThreeSum.EncodedColorResources.half n+1)+2 ≤ 5000000*(_root_.ThreeSum.EncodedColorResources.half n+1)^2
  nlinarith only [Nat.zero_le (_root_.ThreeSum.EncodedColorResources.half n*_root_.ThreeSum.EncodedColorResources.half n)]

































































noncomputable section











end
























end ThreeSum.ThreeSumParameterResources

end

section


/-!
# The physical reporting catalogs use the certified traversal ledger

The switch in every retained catalog is the literal switch used by the
original finite ledger. This module connects the executed level and terminal
costs to those exact binomial terms, preserving the sum over levels.
-/

namespace ThreeSum.SharedTraversalCosts

open Finset Scales LocalCoverBounds LightBlockQuery ReportingHostLevelData
open StageBounds CostLedger
open scoped BigOperators

set_option maxHeartbeats 2400000
set_option maxRecDepth 12000

































































































































open Filter Real Parameters
open scoped Topology

noncomputable section

theorem size_powerBound : PowerBound (fun n => size (_root_.ThreeSum.SharedTraversalCosts.half n) (_root_.ThreeSum.SharedTraversalCosts.blocks n)) 0 := by
  have hh : PowerBound _root_.ThreeSum.SharedTraversalCosts.half 0 := SharedReportingCosts.half_powerBound
  have hj : PowerBound _root_.ThreeSum.SharedTraversalCosts.blocks 0 := SharedReportingCosts.blocks_powerBound
  have hl : PowerBound (fun n => 2048*_root_.ThreeSum.SharedTraversalCosts.half n+20) 0 := by
    have hm : PowerBound (fun n => 2048*_root_.ThreeSum.SharedTraversalCosts.half n) 0 := by
      simpa only [zero_add] using (PowerBound.const 2048).mul hh
    exact hm.add_same (PowerBound.const 20)
  change PowerBound (fun n => (_root_.ThreeSum.SharedTraversalCosts.blocks n+1)*(2048*_root_.ThreeSum.SharedTraversalCosts.half n+20)) 0
  simpa only [zero_add] using (hj.add_same (PowerBound.const 1)).mul hl

theorem overhead_powerBound : PowerBound scaledOverhead 0 := by
  change PowerBound (fun n => 200000*(size (_root_.ThreeSum.SharedTraversalCosts.half n) (_root_.ThreeSum.SharedTraversalCosts.blocks n))^4) 0
  simpa only [zero_add,mul_zero] using (PowerBound.const 200000).mul (size_powerBound.pow 4)

theorem traversal_counts_powerBound (k : ℕ) : PowerBound
    (fun n => initialCount UniformStageBounds.wantedBudget n+
      activeCount (UniformStageBounds.falseBudget k) n+
      terminalCount (UniformStageBounds.falseBudget k) n) certificateExponent := by
  have hi := UniformStageBounds.budget_initial_powerBound.mono_exponent
    (all_costs_le_certificate _ (by simp [costLedger]))
  have ha := (UniformStageBounds.budget_active_powerBound k).mono_exponent
    (all_costs_le_certificate _ (by simp [costLedger]))
  have ht := (UniformStageBounds.budget_terminal_powerBound k).mono_exponent
    (all_costs_le_certificate _ (by simp [costLedger]))
  exact (hi.add_same ha).add_same ht


















end
end ThreeSum.SharedTraversalCosts

end

section


/-!
# Include the executed wanted decoder and scratch-pointer constructor

The actual physical indices have a size-only bound, independently of the
input integer magnitude. Their logarithmic decoder cost and the literal
layout power loop therefore contribute exponent zero. A fixed caller cost
is included explicitly for the remaining register loads and calls.
-/

namespace ThreeSum.SharedTraversalCosts

open Scales StageBounds CostLedger LightBlockQuery

set_option maxHeartbeats 2000000
set_option maxRecDepth 12000



































































open Filter Real Parameters
open scoped Topology

noncomputable section

theorem scalar_overhead_powerBound (c : ℕ) : PowerBound (scalarOverhead c) 0 := by
  have hb := SharedReportingCosts.bits_powerBound
  have hj : PowerBound _root_.ThreeSum.SharedTraversalCosts.blocks 0 := SharedReportingCosts.blocks_powerBound
  have hw : PowerBound (fun n => width (_root_.ThreeSum.SharedTraversalCosts.half n) (_root_.ThreeSum.SharedTraversalCosts.blocks n)) 0 := SharedReportingCosts.width_powerBound
  have hlog : PowerBound (fun n => 8192*(inputBits n+1)+3) 0 := by
    have hh : PowerBound (fun n => 8192*(inputBits n+1)) 0 := by
      simpa only [zero_add] using (PowerBound.const 8192).mul (hb.add_same (PowerBound.const 1))
    exact hh.add_same (PowerBound.const 3)
  have hd : PowerBound (fun n => 800*(_root_.ThreeSum.SharedTraversalCosts.blocks n+1)*(8192*(inputBits n+1)+3)) 0 := by
    simpa only [zero_add] using ((PowerBound.const 800).mul (hj.add_same (PowerBound.const 1))).mul hlog
  have hwidth : PowerBound (fun n => 20*width (_root_.ThreeSum.SharedTraversalCosts.half n) (_root_.ThreeSum.SharedTraversalCosts.blocks n)) 0 := by
    simpa only [zero_add] using (PowerBound.const 20).mul hw
  exact (((hd.add_same (PowerBound.const 8300)).add_same hwidth).add_same
    (PowerBound.const 2520)).add_same (PowerBound.const c)

theorem total_overhead_powerBound (c : ℕ) : PowerBound (totalOverhead c) 0 :=
  overhead_powerBound.add_same (scalar_overhead_powerBound c)

theorem dispatchBudget_powerBound (c k : ℕ) : PowerBound (dispatchBudget c k) certificateExponent := by
  have hp : PowerBound (fun n => totalOverhead c n*
      (initialCount UniformStageBounds.wantedBudget n+
        activeCount (UniformStageBounds.falseBudget k) n+
        terminalCount (UniformStageBounds.falseBudget k) n)) certificateExponent := by
    simpa only [zero_add] using (total_overhead_powerBound c).mul (traversal_counts_powerBound k)
  exact ((PowerBound.const 30).mono_exponent
    (by unfold certificateExponent; norm_num : (0 : ℝ) ≤ certificateExponent)).add_same hp








end
end ThreeSum.SharedTraversalCosts

end

section


/-!
# Charge the actual fixed153 wanted scan and fixed154 header caller

The concrete dispatcher contributes4500 operations, and the ascending
recursion contributes300 per slot. The exact active-branch mass remains
inside the cumulative guard until the original reporting ledger is applied.
-/

namespace ThreeSum.SharedTraversalCosts

open Light Finset Scales BandScales GlobalEncoding RawIncidences RawReporting
open ReportingHostLevelData StageBounds CostLedger
open ReportingHostFrontierLayout Parameters

set_option maxHeartbeats 1800000
set_option maxRecDepth 14000






variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]






































































noncomputable section

theorem color_budget_powerBound (k : ℕ) : PowerBound (colorBudget k) certificateExponent := by
  have hp := EncodedColorReportingCosts.time_powerBound k
  have hr := dispatchBudget_powerBound 4800 k
  exact (hp.add_same hr).add_same ((PowerBound.const 5000).mono_exponent
    (by unfold certificateExponent; norm_num))








end
end ThreeSum.SharedTraversalCosts

end

section


/-! # The finite color scan preserves a per-color power bound -/

namespace ThreeSum.LightColorScanCosts

open ColorParameters LightColorParametersCosts StageBounds

noncomputable section

theorem time_powerBound {T : ℕ → ℕ} {a : ℝ} (hT : PowerBound T a) (ha : 0 ≤ a) :
    PowerBound (fun n => LightColorScanHost.time (T n) n) a := by
  have h100 : PowerBound (fun n => 100*count (width n)) 0 := by
    simpa only [zero_add] using (PowerBound.const 100).mul count_powerBound
  have hround : PowerBound (fun n => 100*count (width n)+T n+3000) a :=
    ((h100.mono_exponent ha).add_same hT).add_same ((PowerBound.const 3000).mono_exponent ha)
  have hmul : PowerBound (fun n => count (width n)*(100*count (width n)+T n+3000)) a := by
    simpa only [zero_add] using count_powerBound.mul hround
  change PowerBound (fun n => count (width n)*(100*count (width n)+T n+3000)+100+100) a
  exact (hmul.add_same ((PowerBound.const 100).mono_exponent ha)).add_same
    ((PowerBound.const 100).mono_exponent ha)






end
end ThreeSum.LightColorScanCosts

end

section


/-! # Charge the executed parameter initialization

The actual square-root and quotient loops are bounded by the band root and
divisor. Polynomial storage envelopes do not replace these time bounds.
-/

namespace ThreeSum.ThreeSumParameterResources

open Light Scales BandScales LocalCoverBounds EncodedColorResources StageBounds
open Filter Parameters ArithmeticStageBounds

set_option maxHeartbeats 1900000
set_option maxRecDepth 14000




theorem time_le_budget (n : ℕ) : LightParameterInit.time n ≤ timeBudget n := by
  have hc := LightScales.time_bound n
  have hl := (LocalParameterBounds.time_bound (LightParameterInit.half n)).trans (local_envelope_le n)
  have hg : LightGlobalSizes.time (LightGlobalSizes.localCount n) (blockCount (inputBits n)) (mu n) ≤
      1000*(_root_.ThreeSum.EncodedColorResources.blocks n+mu n+bandRoot n+bandDivisor n+1) := by
    simpa only [LightGlobalSizes.root,LightGlobalSizes.localCount_pow,LightGlobalSizes.divisor,
      bandRoot,bandDivisor,_root_.ThreeSum.EncodedColorResources.blocks] using
      LightGlobalSizes.time_bound (LightGlobalSizes.localCount n) (blockCount (inputBits n)) (mu n)
  have hs := Nat.sqrt_le_self (inputBits n)
  have he : windowExponent (inputBits n) ≤ inputBits n+1 := by unfold windowExponent; omega
  unfold timeBudget LightParameterInit.time LightNatPower.time sqrtTime
  omega

noncomputable section

theorem timeBudget_powerBound : PowerBound timeBudget 1 := by
  have hsmall : PowerBound (fun n => inputBits n+1+_root_.ThreeSum.EncodedColorResources.blocks n+mu n) 0 :=
    ((SharedReportingCosts.bits_powerBound.add_same (PowerBound.const 1)).add_same
      EncodedColorTime.blocks_powerBound).add_same EncodedColorTime.mu_powerBound
  have hroot : PowerBound bandRoot 1 :=
    (PowerBound.of_rate bandRoot_log_rate).mono_exponent (by have hh := E_bounds.2; linarith)
  have hdiv : PowerBound bandDivisor 1 :=
    (PowerBound.of_rate bandDivisor_log_rate).mono_exponent (by norm_num)
  have hlocal := localEnvelope_powerBound.mono_exponent (by norm_num : (0 : ℝ)≤1)
  have hh := (((hsmall.mono_exponent (by norm_num : (0 : ℝ)≤1)).add_same hroot).add_same hdiv).add_same hlocal
  change PowerBound (fun n => 10000*(inputBits n+1+_root_.ThreeSum.EncodedColorResources.blocks n+mu n+bandRoot n+bandDivisor n+localEnvelope n)) 1
  simpa only [zero_add] using (PowerBound.const 10000).mul hh

theorem time_powerBound : PowerBound LightParameterInit.time 1 :=
  powerBound_mono timeBudget_powerBound (Eventually.of_forall time_le_budget)










end
end ThreeSum.ThreeSumParameterResources

end

section


/-! # Exact outer-driver time from the concrete per-color certificate -/

namespace ThreeSum.ThreeSumColorDriverCosts

open Scales Parameters StageBounds ArithmeticStageBounds

set_option maxHeartbeats 1800000

noncomputable section

theorem time_powerBound {T : ℕ→ℕ} {a : ℝ} (hT : PowerBound T a) (ha : 1≤a) :
    PowerBound (fun n => LightThreeSumFastDriver.time (T n) n) a := by
  have hzero : 0≤a := by linarith
  have hparams := ThreeSumParameterResources.time_powerBound.mono_exponent ha
  have hscan := LightColorScanCosts.time_powerBound hT hzero
  change PowerBound (fun n => LightParameterInit.time n+LightColorScanHost.time (T n) n+500) a
  exact (hparams.add_same hscan).add_same ((PowerBound.const 500).mono_exponent hzero)

theorem time_certificate {T : ℕ→ℕ} (hT : PowerBound T certificateExponent) :
    PowerBound (fun n => LightThreeSumFastDriver.time (T n) n) certificateExponent :=
  time_powerBound hT (by norm_num [certificateExponent])












end
end ThreeSum.ThreeSumColorDriverCosts

end

section


/-!
# The exact hybrid cost along every fixed input-magnitude exponent

The exceptional-size and excessive-magnitude branches use the original
triple scan. Once the size reaches the fixed cutoff, every bound at most
n^κ selects the same fast cost. The scalar exponentiation and fixed caller
cost fit within the proved gap between the certificate and target exponents.
-/

namespace ThreeSum.ThreeSumHybridCosts

open Light Parameters StageBounds Filter

set_option maxHeartbeats 1200000
set_option maxRecDepth 12000












theorem time_of_large {κ cutoff n U : ℕ} (hn : cutoff≤n) (hU : U≤n^κ) :
    time κ cutoff n U=fastTime κ n := by
  simp only [time,fastTime,if_neg (not_or_intro (Nat.not_lt.mpr hn) (Nat.not_lt.mpr hU))]

noncomputable section

theorem fastTime_powerBound (κ : ℕ) : PowerBound (fastTime κ) certificateExponent := by
  have hfast := ThreeSumColorDriverCosts.time_certificate
    (SharedTraversalCosts.color_budget_powerBound κ)
  have hp := (PowerBound.const (LightNatPower.time κ)).mono_exponent
    (show (0 : ℝ)≤certificateExponent by norm_num [certificateExponent])
  have hc := (PowerBound.const 1000).mono_exponent
    (show (0 : ℝ)≤certificateExponent by norm_num [certificateExponent])
  exact (hfast.add_same hp).add_same hc







theorem fastTime_eventually_target (κ : ℕ) :
    ∀ᶠ n : ℕ in atTop, (fastTime κ n : ℝ)≤(n : ℝ)^targetExponent := by
  have hh := fastTime_powerBound κ (targetExponent-certificateExponent)
    (sub_pos.mpr certificate_lt_target)
  simpa only [add_sub_cancel] using hh









theorem timeUpTo_le_fastTime {κ cutoff n : ℕ} {u : ℝ}
    (hn : cutoff≤n) (hu : u≤(n : ℝ)^(κ : ℝ)) :
    timeUpTo (time κ cutoff) n u≤(fastTime κ n : ℝ) := by
  apply timeUpTo_le
  intro U hU
  have hp : 0≤(n : ℝ)^(κ : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hU' : (U : ℝ)≤(n : ℝ)^(κ : ℝ) := hU.trans (max_le hu hp)
  have hUnat : U≤n^κ := by
    rw [Real.rpow_natCast] at hU'
    exact_mod_cast hU'
  rw [time_of_large hn hUnat]

/-- The finite supremum over all input bounds is exactly the fast branch. -/
theorem timeUpTo_eq_fastTime {κ cutoff n : ℕ} (hn : cutoff≤n) :
    timeUpTo (time κ cutoff) n ((n : ℝ)^(κ : ℝ))=(fastTime κ n : ℝ) := by
  apply le_antisymm (timeUpTo_le_fastTime hn le_rfl)
  have hzero : (0 : ℝ)≤(n : ℝ)^(κ : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hh := le_timeUpTo (time κ cutoff) n (U := 0) (u := (n : ℝ)^(κ : ℝ))
    (by simpa only [Nat.cast_zero] using hzero)
  simpa only [time_of_large hn (Nat.zero_le (n^κ))] using hh

theorem timeUpTo_eventually_target (κ cutoff : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      timeUpTo (time κ cutoff) n ((n : ℝ)^(κ : ℝ))≤(n : ℝ)^targetExponent := by
  filter_upwards [fastTime_eventually_target κ,eventually_ge_atTop cutoff] with n ht hn
  simpa only [timeUpTo_eq_fastTime hn] using ht








end
end ThreeSum.ThreeSumHybridCosts

end

section


/-!
# The complete543-procedure original-input solver

For each fixed magnitude exponent, the cutoff is chosen from the proved
uniform parameter conditions. The program tests that cutoff, computes the
integer power, and uses the exact original-triple fallback whenever needed.
Every branch returns the original distinct-position decision and preserves
all memory before the supplied free address.
-/

namespace ThreeSum.LightThreeSumHybrid

open Light ThreeSumApsp.Spec

set_option maxHeartbeats 1400000
set_option maxRecDepth 18000

noncomputable section












































theorem poly_need (κ : ℕ) : PolyNeed (need κ) :=
  ThreeSumFastResourcesHybrid.poly_need κ (ThreeSumWantedHostConditions.cutoff κ)





















end
end ThreeSum.LightThreeSumHybrid

end

section


/-!
# Transfer the verified hybrid solver to the exact end-statement model

The premises below require an actual light-language solver of s3Task with
the frozen hybrid cost and a polynomial resource requirement. The existing
compiler realization supplies the word-RAM program. These interfaces do
not supply or assume away the executable solver obligation.
-/

namespace ThreeSum.ThreeSumHybridEndBridge

open Light

set_option maxHeartbeats 1200000
set_option maxRecDepth 12000

noncomputable section

theorem realized_of_solves {κ cutoff : ℕ} {P : Program} {p : ℕ}
    {need : ℕ→ℕ→Need}
    (hs : Solves s3Task P p (ThreeSumHybridCosts.time κ cutoff) need)
    (hp : PolyNeed need) :
    ThreeSumApsp.WordRam.Realized EndStatement.ThreeSum
      (timeUpTo (ThreeSumHybridCosts.time κ cutoff)) :=
  Light.Sec3.realized_threeSum _ (hs.solvedIn hp)

theorem solvedAt_of_solves {κ cutoff : ℕ} {P : Program} {p : ℕ}
    {need : ℕ→ℕ→Need}
    (hs : Solves s3Task P p (ThreeSumHybridCosts.time κ cutoff) need)
    (hp : PolyNeed need) :
    ThreeSumApsp.WordRam.SolvedInTimeAt EndStatement.ThreeSum κ (981/500 : ℝ) 0 := by
  apply ThreeSumApsp.FromClaims.solvedAt_of_realized
    (timeUpTo (ThreeSumHybridCosts.time κ cutoff)) κ (realized_of_solves hs hp) (C := 1)
  simpa only [pow_zero,mul_one,one_mul,Parameters.targetExponent] using
    ThreeSumHybridCosts.timeUpTo_eventually_target κ cutoff

/-- A family of concrete solver contracts yields the core-Lean rational
end statement, including every fixed magnitude exponent κ=0,1,2,... . -/
theorem endStatement_of_solvers
    (h : ∀ κ : ℕ, ∃ (cutoff : ℕ) (P : Program) (p : ℕ) (need : ℕ→ℕ→Need),
      Solves s3Task P p (ThreeSumHybridCosts.time κ cutoff) need ∧ PolyNeed need) :
    EndStatement.ThreeSum.SolvedInTime (981/500 : Rat) := by
  have hall : ThreeSumApsp.WordRam.SolvedInTime EndStatement.ThreeSum (981/500 : ℝ) 0 := by
    intro κ
    obtain ⟨cutoff,P,p,need,hs,hp⟩ := h κ
    exact solvedAt_of_solves hs hp
  exact hall.endStatement (by norm_num) (by norm_num)

end
end ThreeSum.ThreeSumHybridEndBridge

end

section


/-!
# The complete 3SUM solver at exponent 981/500

For each fixed magnitude exponent, the actual hybrid executable handles
the finite exceptional sizes and arbitrary supplied magnitude bounds.
Its proved polynomial resource requirement permits the existing compiler
realization, and its exact running time satisfies the rational end statement.
-/

namespace ThreeSum

theorem solvedInTime_981_500_sourceProof :
    EndStatement.ThreeSum.SolvedInTime (981/500 : Rat) := by
  apply ThreeSumHybridEndBridge.endStatement_of_solvers
  intro κ
  exact ⟨ThreeSumWantedHostConditions.cutoff κ,LightThreeSumHybrid.program κ,542,
    LightThreeSumHybrid.need κ,LightThreeSumHybrid.solves κ,LightThreeSumHybrid.poly_need κ⟩




end ThreeSum

end


theorem solution : EndStatement.ThreeSum.SolvedInTime 1.962 := by
  have exponent : (1.962 : Rat) = (981 / 500 : Rat) := by norm_num
  simpa only [exponent] using ThreeSum.solvedInTime_981_500_sourceProof


#print axioms solution
