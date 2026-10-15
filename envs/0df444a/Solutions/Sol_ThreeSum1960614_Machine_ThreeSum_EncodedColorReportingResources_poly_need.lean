-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.EncodedColorReportingResources.poly_need
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T09:21:17.607827+00:00
-- url     : https://prove2.me/submissions/8f06797a-7653-4f34-9886-b4f0c875b237

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle039
import Definitions.Def_ThreeSum1960614_Machine_Bundle040
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
import Mathlib.Tactic.IntervalCases
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_EncodedColorResources_dimensions
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_EncodedColorResources_prime_word_bound
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_EncodedColorResources_source_word_bound
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_EncodedColorResources_stage_depth_bound
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightLocalCoverMagnitude_bounds
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightLocalCoverResources_word_polynomial
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LocalParameterBounds_count_word_bound
import Theorems.Thm_ThreeSum_PolynomialResources_pair_polyBound_of_powerBound
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_SharedReportingBankResourceBounds_components
import Theorems.Thm_ThreeSum_StageBounds_PowerBound_add_same
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_ThreeSumReportingSetupResources_poly_need
import Theorems.Thm_ThreeSum_KaratsubaInterface_capacity_lt_twice
import Theorems.Thm_ThreeSum_Scales_natSqrt_ratio_tendsto_zero

private theorem ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.add_same {f g : ℕ → ℕ} {a : ℝ}
    (hf : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound f a)
    (hg : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound g a) :
    _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => f n+g n) a := by
  exact _root_.ThreeSum.StageBounds.PowerBound.add_same hf hg


local instance platformRadixNonzero_2745c4047b (n : ℕ) : NeZero (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) :=
  ⟨Nat.ne_of_gt (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix_pos n)⟩


namespace Filter
end Filter
namespace Light
end Light
namespace Real
end Real
namespace ThreeSum
end ThreeSum
namespace ThreeSum.ArithmeticStageBounds
end ThreeSum.ArithmeticStageBounds
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
namespace ThreeSum.EncodedColorLayout
end ThreeSum.EncodedColorLayout
namespace ThreeSum.EncodedColorReportingResources
end ThreeSum.EncodedColorReportingResources
namespace ThreeSum.EncodedColorResources
end ThreeSum.EncodedColorResources
namespace ThreeSum.KaratsubaInterface
end ThreeSum.KaratsubaInterface
namespace ThreeSum.LightBandRawAResources
end ThreeSum.LightBandRawAResources
namespace ThreeSum.LightLocalCoverInitResources
end ThreeSum.LightLocalCoverInitResources
namespace ThreeSum.LightLocalCoverMagnitude
end ThreeSum.LightLocalCoverMagnitude
namespace ThreeSum.LightLocalCoverResources
end ThreeSum.LightLocalCoverResources
namespace ThreeSum.LightScales
end ThreeSum.LightScales
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalParameterBounds
end ThreeSum.LocalParameterBounds
namespace ThreeSum.MassScales
end ThreeSum.MassScales
namespace ThreeSum.ModuloCosts
end ThreeSum.ModuloCosts
namespace ThreeSum.Parameters
end ThreeSum.Parameters
namespace ThreeSum.PolynomialResources
end ThreeSum.PolynomialResources
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.SharedReportingBankResourceBounds
end ThreeSum.SharedReportingBankResourceBounds
namespace ThreeSum.StageBounds
end ThreeSum.StageBounds
namespace ThreeSum.StageBounds.PowerBound
end ThreeSum.StageBounds.PowerBound
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds
end ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds
namespace ThreeSum1960614.Machine.ThreeSum.BandPartition
end ThreeSum1960614.Machine.ThreeSum.BandPartition
namespace ThreeSum1960614.Machine.ThreeSum.BandScales
end ThreeSum1960614.Machine.ThreeSum.BandScales
namespace ThreeSum1960614.Machine.ThreeSum.CostLedger
end ThreeSum1960614.Machine.ThreeSum.CostLedger
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorLayout
end ThreeSum1960614.Machine.ThreeSum.EncodedColorLayout
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorReportingResources
end ThreeSum1960614.Machine.ThreeSum.EncodedColorReportingResources
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorResources
end ThreeSum1960614.Machine.ThreeSum.EncodedColorResources
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.HierarchyScales
end ThreeSum1960614.Machine.ThreeSum.HierarchyScales
namespace ThreeSum1960614.Machine.ThreeSum.KaratsubaInterface
end ThreeSum1960614.Machine.ThreeSum.KaratsubaInterface
namespace ThreeSum1960614.Machine.ThreeSum.LightBandRawAResources
end ThreeSum1960614.Machine.ThreeSum.LightBandRawAResources
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverInitResources
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverInitResources
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMagnitude
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMagnitude
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverResources
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverResources
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverTables
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverTables
namespace ThreeSum1960614.Machine.ThreeSum.LightScales
end ThreeSum1960614.Machine.ThreeSum.LightScales
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.LocalParameterBounds
end ThreeSum1960614.Machine.ThreeSum.LocalParameterBounds
namespace ThreeSum1960614.Machine.ThreeSum.MassScales
end ThreeSum1960614.Machine.ThreeSum.MassScales
namespace ThreeSum1960614.Machine.ThreeSum.ModuloCosts
end ThreeSum1960614.Machine.ThreeSum.ModuloCosts
namespace ThreeSum1960614.Machine.ThreeSum.Parameters
end ThreeSum1960614.Machine.ThreeSum.Parameters
namespace ThreeSum1960614.Machine.ThreeSum.PolynomialResources
end ThreeSum1960614.Machine.ThreeSum.PolynomialResources
namespace ThreeSum1960614.Machine.ThreeSum.Scales
end ThreeSum1960614.Machine.ThreeSum.Scales
namespace ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds
end ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds
namespace ThreeSum1960614.Machine.ThreeSum.StageBounds
end ThreeSum1960614.Machine.ThreeSum.StageBounds
namespace ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound
end ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound
namespace ThreeSum1960614.Machine.ThreeSum.Switch
end ThreeSum1960614.Machine.ThreeSum.Switch
namespace ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData
end ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData
namespace ThreeSum1960614.Machine.ThreeSum.TrimScales
end ThreeSum1960614.Machine.ThreeSum.TrimScales
namespace ThreeSum1960614.Machine.ThreeSum.UniformStageBounds
end ThreeSum1960614.Machine.ThreeSum.UniformStageBounds
namespace ThreeSum1960614.Machine.ThreeSumApsp.WordRam
end ThreeSum1960614.Machine.ThreeSumApsp.WordRam
namespace ThreeSumApsp.WordRam
end ThreeSumApsp.WordRam

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



























theorem muZero_square_log_ratio_tendsto_zero :
    Tendsto (fun n : ℕ => (_root_.ThreeSum.Scales.muZero n : ℝ) ^ 2 / Real.log n) atTop (𝓝 0) := by
  have h := (_root_.ThreeSum.Scales.microSize_square_ratio_tendsto_zero.comp _root_.ThreeSum.Scales.inputBits_tendsto_atTop).mul
    _root_.ThreeSum.Scales.inputBits_log_ratio_tendsto
  simp only [zero_mul] at h
  apply h.congr'
  filter_upwards [_root_.ThreeSum.Scales.inputBits_tendsto_atTop.eventually (eventually_ge_atTop 1)] with n hn
  have hn0 : (_root_.ThreeSum.Scales.inputBits n : ℝ) ≠ 0 := by exact_mod_cast (by omega : inputBits n ≠ 0)
  simp only [Function.comp_def, _root_.ThreeSum.Scales.muZero]
  field_simp







theorem localSearch_log_ratio_tendsto_zero (C : ℕ) :
    Tendsto (fun n : ℕ => Real.log (_root_.ThreeSum.Scales.localSearch C n : ℝ) / Real.log n) atTop (𝓝 0) := by
  have h := _root_.ThreeSum1960614.Machine.ThreeSum.Scales.muZero_square_log_ratio_tendsto_zero.const_mul ((C : ℝ) * Real.log 2)
  simpa [_root_.ThreeSum.Scales.localSearch, Nat.cast_pow, Nat.cast_mul, Real.log_pow, mul_div_assoc,
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
    ∀ᶠ n : ℕ in atTop, (_root_.ThreeSum.Scales.localSearch C n : ℝ) ≤ (n : ℝ) ^ d := by
  simpa using _root_.ThreeSum1960614.Machine.ThreeSum.Scales.eventually_le_rpow_of_log_ratio (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.localSearch_log_ratio_tendsto_zero C) hd









theorem windowExponent_ratio_tendsto_zero :
    Tendsto (fun m : ℕ => (_root_.ThreeSum.Scales.windowExponent m : ℝ) / m) atTop (𝓝 0) := by
  have h := _root_.ThreeSum.Scales.natSqrt_ratio_tendsto_zero.add
    (tendsto_natCast_atTop_atTop (R := ℝ)).inv_tendsto_atTop
  simpa [_root_.ThreeSum.Scales.windowExponent, Nat.cast_add, add_div, one_div] using h





theorem primeWindow_log_ratio_tendsto_zero :
    Tendsto (fun n : ℕ => Real.log (_root_.ThreeSum.Scales.primeWindow n : ℝ) / Real.log n) atTop (𝓝 0) := by
  have h := ((_root_.ThreeSum1960614.Machine.ThreeSum.Scales.windowExponent_ratio_tendsto_zero.comp _root_.ThreeSum.Scales.inputBits_tendsto_atTop).mul
    _root_.ThreeSum.Scales.inputBits_log_ratio_tendsto).const_mul (Real.log 2)
  simp only [zero_mul, mul_zero] at h
  apply h.congr'
  filter_upwards [_root_.ThreeSum.Scales.inputBits_tendsto_atTop.eventually (eventually_ge_atTop 1)] with n hn
  have hn0 : (_root_.ThreeSum.Scales.inputBits n : ℝ) ≠ 0 := by exact_mod_cast (by omega : inputBits n ≠ 0)
  simp only [Function.comp_def, _root_.ThreeSum.Scales.primeWindow, Nat.cast_pow, Real.log_pow, Nat.cast_ofNat]
  field_simp













theorem muZero_eq_twice_half (n : ℕ) : _root_.ThreeSum.Scales.muZero n = 2 * _root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n) := rfl































































end

end ThreeSum.Scales

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# A polynomial bound in the parameters fits in a word

The running-time claims hold at every word size W ≥ b (log₂ p₁ + ⋯ + log₂ p_r + 1), where p₁, …, p_r
are the parameters of the instance and the slope b is chosen with the program (`Admissible`).  A
light program states its limits as a polynomial in the parameters,
`polyBound s k params` = 2^s ((p₁ + 1) ⋯ (p_r + 1))^k.

The main fact is `polyBound_le`: this bound is at most 2^W as soon as b ≥ s + k r + k.  Each factor
p + 1 is at most 2^(log₂ p + 1) (`prod_succ_le`), so with S the sum of the logarithms the bound is
at most 2^(s + k (S + r)), and s + k (S + r) ≤ (s + k r + k) (S + 1) ≤ W.
-/

@[expose] public section

namespace Light
open _root_.Light


open _root_.ThreeSumApsp.WordRam
open _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam











/-- The bound grows with its two exponents. -/
theorem polyBound_mono {s s' k k' : ℕ} (hs : s ≤ s') (hk : k ≤ k') (params : List ℕ) :
    _root_.Light.polyBound s k params ≤ _root_.Light.polyBound s' k' params := by
  have : 0 < (params.map (· + 1)).prod := List.prod_pos (by simp)
  exact Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) hs) (Nat.pow_le_pow_right this hk)









end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact resource formulas for the original-input band and incidence program

These formulas use the existing selected-color layout without changing any
address or procedure. The physical BC, AB, AC owner records and the packed
value, owner, and sorted-position arrays are all included in the extent.
-/

namespace ThreeSum.LightBandRawAResources
open _root_.ThreeSum.LightBandRawAResources


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.EncodedColorLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorLayout

set_option maxHeartbeats 1800000
set_option maxRecDepth 12000







theorem clog_le_self (n : ℕ) : Nat.clog 2 n ≤ n :=
  Nat.clog_le_of_le_pow (Nat.le_of_lt Nat.lt_two_pow_self)

theorem count_le (n g : ℕ) : _root_.ThreeSum.ColorBandBounds.count n g ≤ 3*n^2 :=
  Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left (_root_.ThreeSum1960614.Machine.ThreeSum.BandPartition.size_le n g) 2)

theorem width_le (n g : ℕ) : _root_.ThreeSum.ColorBandBounds.width n g ≤ 3*n+1 := by
  have hm := _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition.size_le n g
  have hc := _root_.ThreeSum1960614.Machine.ThreeSum.LightBandRawAResources.clog_le_self (_root_.ThreeSum.BandPartition.size n g+_root_.ThreeSum.BandPartition.size n g+_root_.ThreeSum.BandPartition.size n g+1)
  unfold _root_.ThreeSum.ColorBandBounds.width _root_.ThreeSum.LightBandEnumeration.width
  omega



theorem depth_le (W n g : ℕ) : _root_.ThreeSum.LightBandRawAColor.depth W n g ≤ W+5*n+21 := by
  have hc := _root_.ThreeSum1960614.Machine.ThreeSum.LightBandRawAResources.clog_le_self n
  have hw := _root_.ThreeSum1960614.Machine.ThreeSum.LightBandRawAResources.width_le n g
  unfold _root_.ThreeSum.LightBandRawAColor.depth _root_.ThreeSum.LightColorBands.depth _root_.ThreeSum.ColorBandBounds.depth
  omega

end ThreeSum.LightBandRawAResources

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Actual initialization of the integer block schedule

The fixed program computes all initial size parameters from the input
length. It uses the benchmark's proved logarithm, ceiling cube-root and
ceiling-half loops, with exact rounding bridges below. Division is used
only through an actual counting routine on the logarithmic numerator.
-/

namespace ThreeSum.LightScales
open _root_.ThreeSum.LightScales


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}

theorem inputBits_le_self (n : ℕ) : _root_.ThreeSum.Scales.inputBits n ≤ n := by
  simpa [_root_.ThreeSum.Scales.inputBits,Nat.log2_eq_log_two] using Nat.log_le_self 2 n

































end ThreeSum.LightScales

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Local parameter construction fits the uniform subpolynomial budget

These bounds apply to the actual operational contracts, including the
primality scans and integer division. The deliberately loose envelope is
only used for a microblock whose half-size is a cube root of `log n`.
-/

namespace ThreeSum.LocalParameterBounds
open _root_.ThreeSum.LocalParameterBounds


open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds

set_option maxHeartbeats 1000000




theorem pow_pos (e : ℕ) : 1 ≤ (2 : ℕ)^e := Nat.pos_iff_ne_zero.mpr (pow_ne_zero _ (by decide))

theorem threshold_bound (h : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localThreshold h ≤ 2^(514*h) := by
  calc
    _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localThreshold h ≤ 2^(464*h)*2^(2*h) :=
      Nat.mul_le_mul_right _ (Nat.choose_le_two_pow _ _)
    _ ≤ 2^(514*h) := by
      rw [← pow_add]
      exact Nat.pow_le_pow_right (by decide) (by omega)

theorem vertex_bound (h : ℕ) : _root_.ThreeSum.LocalCoverBounds.vertexCount (464*h) h ≤ 2^(514*h) :=
  (Nat.choose_le_two_pow _ _).trans (Nat.pow_le_pow_right (by decide) (by omega))

theorem root_bound (h : ℕ) : _root_.ThreeSum.LocalCoverBounds.rootCeiling (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localThreshold h) ≤ 2*2^(514*h) := by
  have hs := Nat.sqrt_le_self (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localThreshold h-1)
  have ht := _root_.ThreeSum1960614.Machine.ThreeSum.LocalParameterBounds.threshold_bound h
  have hp := _root_.ThreeSum1960614.Machine.ThreeSum.LocalParameterBounds.pow_pos (514*h)
  unfold _root_.ThreeSum.LocalCoverBounds.rootCeiling
  omega

theorem prime_bound (h : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h ≤ 2^(514*h+2) := by
  have hp := (_root_.ThreeSum.LocalCoverBounds.selectedPrime_spec (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localThreshold h)).2.2
  have hr := _root_.ThreeSum1960614.Machine.ThreeSum.LocalParameterBounds.root_bound h
  change _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h ≤ _ at hp
  rw [pow_add]
  norm_num
  omega













theorem selected_word_bound (h : ℕ) :
    _root_.ThreeSum.LightSelectedPrime.word (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localThreshold h) ≤ 2^(514*h+8) := by
  have ht := _root_.ThreeSum1960614.Machine.ThreeSum.LocalParameterBounds.threshold_bound h
  have hx := _root_.ThreeSum1960614.Machine.ThreeSum.LocalParameterBounds.pow_pos (514*h)
  unfold _root_.ThreeSum.LightSelectedPrime.word
  rw [pow_add]
  norm_num
  omega

theorem cap_word_bound (h : ℕ) :
    20*(_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h+_root_.ThreeSum.LocalCoverBounds.vertexCount (464*h) h+1) ≤ 2^(514*h+7) := by
  have hp := _root_.ThreeSum1960614.Machine.ThreeSum.LocalParameterBounds.prime_bound h
  have hv := _root_.ThreeSum1960614.Machine.ThreeSum.LocalParameterBounds.vertex_bound h
  have hx := _root_.ThreeSum1960614.Machine.ThreeSum.LocalParameterBounds.pow_pos (514*h)
  rw [pow_add] at hp
  norm_num at hp
  rw [pow_add]
  norm_num
  omega

theorem word_bound (h : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalParameters.word h ≤ _root_.ThreeSum.LocalParameterBounds.envelope h := by
  have hc : _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCounts.word h ≤ _root_.ThreeSum.LocalParameterBounds.base h :=
    (_root_.ThreeSum1960614.Machine.ThreeSum.LocalParameterBounds.count_word_bound h).trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hp : _root_.ThreeSum.LightSelectedPrime.word (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localThreshold h) ≤ _root_.ThreeSum.LocalParameterBounds.base h :=
    (_root_.ThreeSum1960614.Machine.ThreeSum.LocalParameterBounds.selected_word_bound h).trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hd : 20*(_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h+_root_.ThreeSum.LocalCoverBounds.vertexCount (464*h) h+1) ≤ _root_.ThreeSum.LocalParameterBounds.base h :=
    (_root_.ThreeSum1960614.Machine.ThreeSum.LocalParameterBounds.cap_word_bound h).trans (Nat.pow_le_pow_right (by decide) (by omega))
  have he : _root_.ThreeSum.LocalParameterBounds.envelope h = 4*_root_.ThreeSum.LocalParameterBounds.base h := by unfold _root_.ThreeSum.LocalParameterBounds.envelope _root_.ThreeSum.LocalParameterBounds.base; rw [pow_add]; norm_num; omega
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalParameters.word
  rw [he]
  omega











end ThreeSum.LocalParameterBounds

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

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
open _root_.ThreeSum.MassScales


open _root_.Filter
open _root_.Real
open _root_.ThreeSum.Parameters
open _root_.ThreeSum1960614.Machine.ThreeSum.Parameters
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales
open scoped _root_.Topology

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000























noncomputable section





theorem nat_log_rate_const (c : ℕ) :
    Tendsto (fun n : ℕ => Real.log (c : ℝ) / Real.log n) atTop (𝓝 0) := by
  simpa only [mul_zero, Pi.inv_apply, div_eq_mul_inv] using
    _root_.ThreeSum.Asymptotics.log_nat_tendsto_atTop.inv_tendsto_atTop.const_mul (Real.log (c : ℝ))





























end
end ThreeSum.MassScales

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The complete local-cover program fits the uniform local-search budget

Every bound below is for the actual fixed program, including mask and
coefficient construction, counting division, histograms, matrix assembly,
the original greedy loop, and selected-row gathering.
-/

namespace ThreeSum.LightLocalCoverResources
open _root_.ThreeSum.LightLocalCoverResources


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverTables
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout
open _root_.ThreeSum.LightLocalCoverMagnitude
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMagnitude

set_option maxHeartbeats 1800000











theorem word_bound (h : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSetup.word h ≤ _root_.ThreeSum.LightLocalCoverResources.envelope h := by
  have hs : 1 ≤ (h+1)^2 := Nat.pow_pos (by omega)
  calc
    _ ≤ 2000*(_root_.ThreeSum.LightLocalCoverMagnitude.magnitude h)^2 := _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverResources.word_polynomial (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMagnitude.bounds h)
    _ ≤ 2^11*(_root_.ThreeSum.LightLocalCoverMagnitude.magnitude h)^2 := Nat.mul_le_mul_right _ (by decide)
    _ = 2^(11+600000*(h+1)^2*2) := by rw [_root_.ThreeSum.LightLocalCoverMagnitude.magnitude,← pow_mul,← pow_add]
    _ ≤ _root_.ThreeSum.LightLocalCoverResources.envelope h := Nat.pow_le_pow_right (by decide) (by omega)


















end ThreeSum.LightLocalCoverResources

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The six principal finite stage counts

This module assembles actual natural-number work quantities.  Its final
theorem is a runtime-ledger target, not a 3SUM correctness or machine-time
theorem.  The only input-dependent assumptions are four explicit finite
counting inequalities for the wanted mass and the prime-chain score.
An implementation must still connect its operation counter to these counts.
-/

namespace ThreeSum.StageBounds
open _root_.ThreeSum.StageBounds


open _root_.Filter
open _root_.Real
open _root_.ThreeSum.Parameters
open _root_.ThreeSum1960614.Machine.ThreeSum.Parameters
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum1960614.Machine.ThreeSum.Switch
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales
open _root_.ThreeSum.MassScales
open _root_.ThreeSum1960614.Machine.ThreeSum.MassScales
open scoped _root_.Topology

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000





















noncomputable section



namespace PowerBound
open _root_.ThreeSum.StageBounds.PowerBound


theorem of_rate {f : ℕ → ℕ} {a : ℝ}
    (hf : Tendsto (fun n : ℕ => Real.log (f n : ℝ) / Real.log n) atTop (𝓝 a)) : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound f a :=
  fun _ hd => _root_.ThreeSum1960614.Machine.ThreeSum.Scales.eventually_le_rpow_of_log_ratio hf hd

theorem const (c : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun _ => c) 0 := _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.of_rate (_root_.ThreeSum1960614.Machine.ThreeSum.MassScales.nat_log_rate_const c)

theorem mul {f g : ℕ → ℕ} {a b : ℝ} (hf : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound f a) (hg : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound g b) :
    _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => f n * g n) (a + b) := by
  intro d hd
  filter_upwards [hf (d / 2) (by linarith), hg (d / 2) (by linarith),
    eventually_ge_atTop (1 : ℕ)] with n hfn hgn hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  rw [Nat.cast_mul]
  calc
    _ ≤ (n : ℝ) ^ (a + d / 2) * (n : ℝ) ^ (b + d / 2) :=
      mul_le_mul hfn hgn (Nat.cast_nonneg _) (Real.rpow_nonneg hnR.le _)
    _ = (n : ℝ) ^ ((a + b) + d) := by rw [← Real.rpow_add hnR]; congr 1; ring

theorem mono_exponent {f : ℕ → ℕ} {a b : ℝ} (hf : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound f a) (hab : a ≤ b) :
    _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound f b := by
  intro d hd
  filter_upwards [hf d hd, eventually_ge_atTop (1 : ℕ)] with n hn hge
  exact hn.trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hge) (by linarith))



theorem pow {f : ℕ → ℕ} {a : ℝ} (hf : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound f a) (k : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => f n ^ k) ((k : ℝ) * a) := by
  induction k with
  | zero => simpa only [Nat.cast_zero, zero_mul, pow_zero] using _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 1
  | succ k ih =>
      simpa only [Nat.pow_succ, Nat.cast_add, Nat.cast_one, add_mul, one_mul] using ih.mul hf

end PowerBound

































end
end ThreeSum.StageBounds

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The arithmetic and balancing work outside the six reporting stages

The finite bounds here include complete modular-counting invocations, their
signed-remainder bit cost, and the actual correlation/minimum routine. They
augment the six-stage reporting budget. The whole solver still has to charge
its actual host operations to this combined budget.
-/

namespace ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum.ArithmeticStageBounds


open _root_.Filter
open _root_.Real
open _root_.ThreeSum.Parameters
open _root_.ThreeSum1960614.Machine.ThreeSum.Parameters
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales
open _root_.ThreeSum.MassScales
open _root_.ThreeSum1960614.Machine.ThreeSum.MassScales
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.UniformStageBounds
open _root_.ThreeSum.ModuloCosts
open _root_.ThreeSum1960614.Machine.ThreeSum.ModuloCosts
open scoped _root_.Topology

set_option maxHeartbeats 1000000























noncomputable section

theorem powerBound_mono {f g : ℕ → ℕ} {a : ℝ} (hg : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound g a)
    (hfg : ∀ᶠ n : ℕ in atTop, f n ≤ g n) : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound f a := by
  intro d hd
  filter_upwards [hg d hd, hfg] with n hn hm
  exact (show (f n : ℝ) ≤ (g n : ℝ) by exact_mod_cast hm).trans hn



theorem window_powerBound : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound _root_.ThreeSum.Scales.primeWindow 0 :=
  _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.of_rate _root_.ThreeSum1960614.Machine.ThreeSum.Scales.primeWindow_log_ratio_tendsto_zero

theorem maxMod_powerBound : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon*(_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E+1/2)) := by
  change _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n*(4*_root_.ThreeSum.Scales.primeWindow n)^2) (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon*(_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E+1/2))
  have hwindow := ((_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 4).mul _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.window_powerBound).pow 2
  have hh := (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.of_rate _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix_log_ratio_tendsto).mul hwindow
  simpa only [zero_add, mul_zero, add_zero] using hh











theorem identity_powerBound : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n : ℕ => n) 1 := by
  intro d hd
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  simpa only [Real.rpow_one] using
    (Real.rpow_le_rpow_of_exponent_le hnR (show (1 : ℝ) ≤ 1+d by linarith))















end
end ThreeSum.ArithmeticStageBounds

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Resource bounds for the complete h-and-free local-cover initializer -/

namespace ThreeSum.LightLocalCoverInitResources
open _root_.ThreeSum.LightLocalCoverInitResources


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverTables
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout

set_option maxHeartbeats 1500000



theorem parameters_envelope_le (h : ℕ) :
    _root_.ThreeSum.LocalParameterBounds.envelope h ≤ _root_.ThreeSum.LightLocalCoverResources.envelope h := by
  unfold _root_.ThreeSum.LocalParameterBounds.envelope _root_.ThreeSum.LightLocalCoverResources.envelope
  apply Nat.pow_le_pow_right (by decide)
  nlinarith only [Nat.zero_le (h*h)]



theorem four_envelope_le (h : ℕ) :
    4*_root_.ThreeSum.LightLocalCoverResources.envelope h ≤ _root_.ThreeSum.LightLocalCoverInitResources.envelope h := by
  have hs : 1 ≤ (h+1)^2 := Nat.pow_pos (by omega)
  calc
    _ = 2^2*2^(4000000*(h+1)^2) := rfl
    _ = 2^(2+4000000*(h+1)^2) := (pow_add _ _ _).symm
    _ ≤ _root_.ThreeSum.LightLocalCoverInitResources.envelope h := Nat.pow_le_pow_right (by decide) (by omega)





theorem word_bound (h : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverInit.word h ≤ _root_.ThreeSum.LightLocalCoverInitResources.envelope h := by
  have hp := (_root_.ThreeSum1960614.Machine.ThreeSum.LocalParameterBounds.word_bound h).trans (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverInitResources.parameters_envelope_le h)
  have hc := _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverResources.word_bound h
  apply (show _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverInit.word h ≤ 4*_root_.ThreeSum.LightLocalCoverResources.envelope h from ?_).trans
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverInitResources.four_envelope_le h)
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverInit.word
  omega





theorem envelope_le_search {n : ℕ} (hh : 1 ≤ _root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) :
    _root_.ThreeSum.LightLocalCoverInitResources.envelope (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) ≤ _root_.ThreeSum.Scales.localSearch 5000000 n := by
  unfold _root_.ThreeSum.LightLocalCoverInitResources.envelope _root_.ThreeSum.Scales.localSearch
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.Scales.muZero_eq_twice_half]
  apply Nat.pow_le_pow_right (by decide)
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_left
  omega














end ThreeSum.LightLocalCoverInitResources

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# From proved resource envelopes to the compiler's polynomial limits

An eventual power bound supplies a single polynomial valid at every input
size, by explicitly absorbing its finitely many exceptions. Multiplying
by a fixed power of the input magnitude then gives the exact two-parameter
`Light.PolyNeed` required by the verified compiler. These lemmas do not
supply resource envelopes for an algorithm; callers must prove those.
-/

namespace ThreeSum.PolynomialResources
open _root_.ThreeSum.PolynomialResources


open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.Filter
open _root_.Real
open scoped _root_.Topology

noncomputable section







theorem polyNeed_of_envelope {need : ℕ → ℕ → _root_.ThreeSum1960614.Machine.Light.Need} {f : ℕ → ℕ} {a : ℝ}
    (hf : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound f a) (e : ℕ)
    (hword : ∀ n U, (need n U).word ≤ f n*(U+1)^e)
    (hcells : ∀ n U, (need n U).cells ≤ f n*(U+1)^e)
    (hdepth : ∀ n U, (need n U).depth ≤ f n*(U+1)^e) : _root_.ThreeSum1960614.Machine.Light.PolyNeed need := by
  obtain ⟨s,k,h⟩ := _root_.ThreeSum.PolynomialResources.pair_polyBound_of_powerBound hf e
  exact ⟨s,k,fun n U => ⟨(hword n U).trans (h n U),
    (hcells n U).trans (h n U),(hdepth n U).trans (h n U)⟩⟩



end
end ThreeSum.PolynomialResources

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Polynomial limits for the actual shared reporting host

The finite word, cell, and depth formulas are bounded at every input size.
The resulting `Need` includes the complete executed host, while its time
bound remains the exact shared-box budget proved separately.
-/

namespace ThreeSum.SharedReportingBankResourceBounds
open _root_.ThreeSum.SharedReportingBankResourceBounds


open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.Filter
open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open scoped _root_.Topology

set_option maxHeartbeats 1200000
set_option maxRecDepth 14000

noncomputable section

theorem bits_power_powerBound : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => 2^(_root_.ThreeSum.Scales.inputBits n)) 1 := by
  apply _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.powerBound_mono _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.identity_powerBound
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  simpa only [_root_.ThreeSum.Scales.inputBits,Nat.log2_eq_log_two] using
    Nat.pow_log_le_self 2 (by omega : n ≠ 0)

theorem magnitude_powerBound : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound _root_.ThreeSum.SharedReportingBankResourceBounds.magnitude 2048 := by
  have hh := (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const (2^2048)).mul (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.bits_power_powerBound.pow 2048)
  have he : _root_.ThreeSum.SharedReportingBankResourceBounds.magnitude = fun n => 2^2048*(2^(_root_.ThreeSum.Scales.inputBits n))^2048 := by
    funext n
    unfold _root_.ThreeSum.SharedReportingBankResourceBounds.magnitude
    rw [show 2048*(_root_.ThreeSum.Scales.inputBits n+1)=2048+_root_.ThreeSum.Scales.inputBits n*2048 by omega,pow_add,pow_mul]
  rw [he]
  simpa only [Nat.cast_ofNat,mul_one,zero_add] using hh

















end
end ThreeSum.SharedReportingBankResourceBounds

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # A proved polynomial scale for the selected-color program's dimensions -/

namespace ThreeSum.EncodedColorResources
open _root_.ThreeSum.EncodedColorResources


open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.Filter

set_option maxHeartbeats 2200000
set_option maxRecDepth 13000







theorem scale_bounds (n : ℕ) : 100 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n ∧ n+1 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n ∧
    _root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n ∧ _root_.ThreeSum.EncodedColorResources.localEnvelope n ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n ∧
    _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n ∧ _root_.ThreeSum.Scales.primeWindow n ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale
  omega

theorem local_bounds (n : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMagnitude.Bounds (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n) := by
  have hm : _root_.ThreeSum.LightLocalCoverMagnitude.magnitude (_root_.ThreeSum.EncodedColorResources.half n) ≤ _root_.ThreeSum.EncodedColorResources.localEnvelope n := by
    unfold _root_.ThreeSum.LightLocalCoverMagnitude.magnitude _root_.ThreeSum.EncodedColorResources.localEnvelope _root_.ThreeSum.LightLocalCoverInitResources.envelope
    exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (by decide : 600000 ≤ 5000000))
  have hs := hm.trans (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale_bounds n).2.2.2.1
  have H := _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMagnitude.bounds (_root_.ThreeSum.EncodedColorResources.half n)
  exact ⟨H.positive.trans hs,H.width.trans hs,H.vertices.trans hs,H.prime.trans hs,
    H.cap.trans hs,H.candidates.trans hs,H.rounds.trans hs,H.decodePower.trans hs,H.maskPower.trans hs⟩



theorem powers (n : ℕ) : 2^(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.width n+1) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n ∧
    _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks n) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n ∧
    _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime (_root_.ThreeSum.EncodedColorResources.half n)^(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks n)*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime (_root_.ThreeSum.EncodedColorResources.half n) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n ∧
    2^(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks n) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n := by
  have H := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.components n
  have hm := (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale_bounds n).2.2.1
  refine ⟨H.widthPower.trans hm,H.occurrence.trans hm,H.primePower.trans hm,?_⟩
  have htwo : (2 : ℕ) ≤ 2^(464*_root_.ThreeSum.EncodedColorResources.half n)+1 := by have hh := Nat.two_pow_pos (464*_root_.ThreeSum.EncodedColorResources.half n); omega
  exact (Nat.pow_le_pow_left htwo (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks n)).trans (H.radixPower.trans hm)

theorem modulus_le (n : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks n) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n := by
  exact (Nat.le_mul_of_pos_right _ (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime_pos (_root_.ThreeSum.EncodedColorResources.half n))).trans (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.powers n).2.2.1



theorem radix_power_le (n : ℕ) : (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime (_root_.ThreeSum.EncodedColorResources.half n)+1)^(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks n) ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n)^2 := by
  have hp := _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime_pos (_root_.ThreeSum.EncodedColorResources.half n)
  have hmod := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.modulus_le n
  calc
    _ ≤ (2*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime (_root_.ThreeSum.EncodedColorResources.half n))^(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks n) := Nat.pow_le_pow_left (by omega) _
    _ = 2^(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks n)*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime (_root_.ThreeSum.EncodedColorResources.half n)^(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks n) := mul_pow _ _ _
    _ ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n*_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n := Nat.mul_le_mul (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.powers n).2.2.2 hmod
    _ = _ := by ring





theorem totalKeys_le (n : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.totalKeys (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks n) ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n)^2 := by
  have hq : _root_.ThreeSum.LocalCoverBounds.outputCount (464*_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum.EncodedColorResources.half n)^(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks n) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n := by
    calc
      _ ≤ (2^(464*_root_.ThreeSum.EncodedColorResources.half n))^(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks n) := Nat.pow_le_pow_left (Nat.choose_le_two_pow _ _) _
      _ = 2^(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.width n) := by unfold _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.width; rw [← pow_mul]; congr 1; ring
      _ ≤ 2^(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.width n+1) := Nat.pow_le_pow_right (by decide) (by omega)
      _ ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n := (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.powers n).1
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.totalKeys _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys.localCount
  rw [mul_pow]
  exact (Nat.mul_le_mul (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.powers n).2.1 hq).trans_eq (pow_two _).symm

theorem keyBound_le (n : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.keyBound (_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n) (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks n) ≤ 3*(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n)^4 := by
  have hP := (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale_bounds n).2.2.2.2.1
  have hL : 464*_root_.ThreeSum.EncodedColorResources.half n ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n := by have h := (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.local_bounds n).width; omega
  have hp : _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime (_root_.ThreeSum.EncodedColorResources.half n) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n := by have h := (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.local_bounds n).prime; omega
  have hm := Nat.mul_le_mul (Nat.mul_le_mul hL hp) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.radix_power_le n)
  have hs4 : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n)^4 := Nat.le_self_pow (by decide) _
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.keyBound
  nlinarith only [hm,hP,hs4]

noncomputable section

theorem localEnvelope_powerBound : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound _root_.ThreeSum.EncodedColorResources.localEnvelope 0 := by
  refine _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.powerBound_mono (g := _root_.ThreeSum.Scales.localSearch 5000000) ?_ ?_
  · intro d hd
    simpa only [zero_add] using _root_.ThreeSum1960614.Machine.ThreeSum.Scales.localSearch_subpolynomial 5000000 hd
  · filter_upwards [(_root_.ThreeSum.Scales.microHalf_tendsto_atTop.comp _root_.ThreeSum.Scales.inputBits_tendsto_atTop).eventually
      (eventually_ge_atTop 1)] with n hn
    exact _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverInitResources.envelope_le_search hn

theorem scale_powerBound : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale 2048 := by
  have hl := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.localEnvelope_powerBound.mono_exponent (by norm_num : (0 : ℝ) ≤ 2048)
  have hp := _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod_powerBound.mono_exponent (show _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon*(_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E+1/2) ≤ (2048 : ℝ) by
    have hh := _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E_bounds.2; unfold _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon; linarith)
  have hy := _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.window_powerBound.mono_exponent (by norm_num : (0 : ℝ) ≤ 2048)
  have hn := _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.identity_powerBound.mono_exponent (by norm_num : (1 : ℝ) ≤ 2048)
  have hc := (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 100).mono_exponent (by norm_num : (0 : ℝ) ≤ 2048)
  exact ((((_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.magnitude_powerBound.add_same hl).add_same hp).add_same hy).add_same hn).add_same hc

end
end ThreeSum.EncodedColorResources

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Polynomial bounds for the retained local cover and complete global key array -/

namespace ThreeSum.EncodedColorResources
open _root_.ThreeSum.EncodedColorResources


open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds

set_option maxHeartbeats 2000000
set_option maxRecDepth 12000











theorem global_keys_word_bound (n : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys.word (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks n) ≤ 1000*(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n)^5 := by
  have hb := (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale_bounds n).1
  have H := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.local_bounds n
  have hL := H.width
  have hP := H.prime
  have hS := H.rounds
  have hJ := (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.dimensions n).2.1
  have hpow : 2^(464*_root_.ThreeSum.EncodedColorResources.half n+1) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n := by have hh := H.maskPower; omega
  have hprod := Nat.mul_le_mul hL (show _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime (_root_.ThreeSum.EncodedColorResources.half n) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n by omega)
  have hLP := Nat.mul_le_mul (show 464*_root_.ThreeSum.EncodedColorResources.half n ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n by omega) (show _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime (_root_.ThreeSum.EncodedColorResources.half n) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n by omega)
  have hkey := Nat.mul_le_mul (show _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime (_root_.ThreeSum.EncodedColorResources.half n) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n by omega)
    (Nat.mul_le_mul hLP (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.radix_power_le n))
  have hp5 : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n)^5 := Nat.le_self_pow (by decide) _
  have hp25 := Nat.pow_le_pow_right (by omega : 1 ≤ scale n) (by decide : 2 ≤ 5)
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys.word _root_.ThreeSum.LightLocalKeys.word _root_.ThreeSum.LightLocalKeyRow.word _root_.ThreeSum.LightOneHot.word
    _root_.ThreeSum.LightRadixKeys.word _root_.ThreeSum.LightRadixRows.word
  nlinarith only [hb,hL,hP,hS,hJ,hpow,hprod,hLP,hkey,hp5,hp25]

theorem cover_word_bound (n : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeys.word (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks n) ≤ 1000*(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n)^5 := by
  have hlocal := (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverInitResources.word_bound (_root_.ThreeSum.EncodedColorResources.half n)).trans (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale_bounds n).2.2.2.1
  have hp5 : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n)^5 := Nat.le_self_pow (by decide) _
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeys.word
  exact max_le (by omega) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.global_keys_word_bound n)

end ThreeSum.EncodedColorResources

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Affine storage and finite word bounds for the unchanged prime host -/

namespace ThreeSum.EncodedColorResources
open _root_.ThreeSum.EncodedColorResources


open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.EncodedColorLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorLayout
open _root_.ThreeSum.KaratsubaInterface
open _root_.ThreeSum1960614.Machine.ThreeSum.KaratsubaInterface

set_option maxHeartbeats 2400000
set_option maxRecDepth 13000

theorem count_le (n : ℕ) : _root_.ThreeSum.ColorBandBounds.count n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) ≤ 3*(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n)^2 := by
  have hn : n ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n := by have h := (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale_bounds n).2.1; omega
  exact (_root_.ThreeSum1960614.Machine.ThreeSum.LightBandRawAResources.count_le n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)).trans (Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left hn 2))

theorem incidence_cap_le (n : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorStageCosts.incidenceCap n ≤ 3*(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n)^3 := by
  have hh := Nat.mul_le_mul (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.dimensions n).2.2.2.1 (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.count_le n)
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorStageCosts.incidenceCap
  nlinarith only [hh]

























theorem prime_depth_bound (n : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPrimeHost.depth n ≤ 10*_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n := by
  have hb := (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale_bounds n).1
  have hn := (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale_bounds n).2.1
  have hW := (Nat.add_le_add_right (_root_.ThreeSum1960614.Machine.ThreeSum.LightScales.inputBits_le_self n) 1).trans hn
  have hp := (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale_bounds n).2.2.2.2.1
  have hraw := _root_.ThreeSum1960614.Machine.ThreeSum.LightBandRawAResources.depth_le (_root_.ThreeSum.Scales.inputBits n+1) n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)
  have hc := (_root_.ThreeSum1960614.Machine.ThreeSum.LightBandRawAResources.clog_le_self (_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n)).trans hp
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPrimeHost.depth
  apply max_le <;> omega

end ThreeSum.EncodedColorResources

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Finite affine resource bounds for balanced wanted records and shared sources -/

namespace ThreeSum.EncodedColorResources
open _root_.ThreeSum.EncodedColorResources


open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.KaratsubaInterface
open _root_.ThreeSum1960614.Machine.ThreeSum.KaratsubaInterface

set_option maxHeartbeats 2400000
set_option maxRecDepth 13000





theorem wanted_word_bound (n U : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.word (_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks n) U
      (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorStageCosts.incidenceCap n) ≤ 150000*(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n)^9+4*U := by
  have hb := (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale_bounds n).1
  have hlen := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.incidence_cap_le n
  have hG := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.totalKeys_le n
  have hM := (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.dimensions n).2.2.2.2
  have hP := (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale_bounds n).2.2.2.2.1
  have hbound := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.keyBound_le n
  have hcover := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.cover_word_bound n
  have hcapacity := (_root_.ThreeSum.KaratsubaInterface.capacity_lt_twice (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix_pos n)).le.trans (Nat.mul_le_mul_left 2 hM)
  have hp3 : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n)^3 := Nat.le_self_pow (by decide) _
  have hp23 := Nat.pow_le_pow_right (by omega : 1 ≤ scale n) (by decide : 2 ≤ 3)
  have hp9 : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n)^9 := Nat.le_self_pow (by decide) _
  have hp49 := Nat.pow_le_pow_right (by omega : 1 ≤ scale n) (by decide : 4 ≤ 9)
  have hp59 := Nat.pow_le_pow_right (by omega : 1 ≤ scale n) (by decide : 5 ≤ 9)
  have hN : 3*_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorStageCosts.incidenceCap n+_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.totalKeys (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks n)+1 ≤
      11*(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n)^3 := by nlinarith only [hb,hlen,hG,hp3,hp23]
  have hkar : _root_.ThreeSum.LightKaratsuba.wordBound (_root_.ThreeSum.KaratsubaInterface.capacity (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n))
      (3*_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorStageCosts.incidenceCap n+_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.totalKeys (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks n)) ≤
      123904*(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n)^9 := by
    unfold _root_.ThreeSum.LightKaratsuba.wordBound
    calc
      _ ≤ 128*(2*_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n)^3*(11*(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n)^3)^2 := by gcongr
      _ = _ := by ring
  have hbalanced : _root_.ThreeSum.LightBalancedWanted.word (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) (3*_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorStageCosts.incidenceCap n)
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.totalKeys (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks n))
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.keyBound (_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n) (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks n)) ≤ 150000*(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n)^9 := by
    unfold _root_.ThreeSum.LightBalancedWanted.word _root_.ThreeSum.LightOriginalOffset.word _root_.ThreeSum.LightSourceResidues.word
    apply max_le <;> nlinarith only [hb,hM,hbound,hkar,hp9,hp49]
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.word
  refine max_le ?_ (max_le ?_ ?_)
  · nlinarith only [hcover,hp59]
  · unfold _root_.ThreeSum.LightRawAKeys.word
    nlinarith only [hb,hP,hp9]
  · omega



theorem stage_word_bound (n U : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorStageCosts.word n (_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) U (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorStageCosts.incidenceCap n) ≤
      150000*(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n)^9+4*U := by
  have hw := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.wanted_word_bound n U
  have hs := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.source_word_bound n U
  have hp39 := Nat.pow_le_pow_right (by have h := (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale_bounds n).1; omega : 1 ≤ scale n) (by decide : 3 ≤ 9)
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorStageCosts.word _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorWantedSources.word
  exact max_le hw (by omega)



end ThreeSum.EncodedColorResources

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Polynomial Need for the exact closed selected-color pipeline -/

namespace ThreeSum.EncodedColorResources
open _root_.ThreeSum.EncodedColorResources


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds

set_option maxHeartbeats 2000000
set_option maxRecDepth 12000



theorem pipeline_word_bound (n U : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPipeline.word n U ≤ 200000*(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n)^9+9*U := by
  have hb := (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale_bounds n).1
  have hprime := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.prime_word_bound n U
  have hstage := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.stage_word_bound n U
  have hcap := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.incidence_cap_le n
  have hP := (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale_bounds n).2.2.2.2.1
  have hM := (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.dimensions n).2.2.2.2
  have hg := (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.dimensions n).2.2.2.1
  have hh := (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.local_bounds n).width
  have hJ := (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.dimensions n).2.1
  have hcut := (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.dimensions n).2.2.1
  have hS := (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.powers n).2.1
  have hp9 : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n)^9 := Nat.le_self_pow (by decide) _
  have hp39 := Nat.pow_le_pow_right (by omega : 1 ≤ scale n) (by decide : 3 ≤ 9)
  have hp69 := Nat.pow_le_pow_right (by omega : 1 ≤ scale n) (by decide : 6 ≤ 9)
  have hmax : max (_root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPrimeHost.inputWord n U)
      (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorStageCosts.word n (_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) U (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorStageCosts.incidenceCap n)) ≤
      150000*(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n)^9+9*U := max_le (by omega) (by omega)
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPipeline.word
  change max (_root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPrimeHost.inputWord n U)
    (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorStageCosts.word n (_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) U (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorStageCosts.incidenceCap n))+
    _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorStageCosts.incidenceCap n+_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n+_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n+_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n+_root_.ThreeSum.EncodedColorResources.half n+_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks n+_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n+
    _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks n)+100 ≤ _
  nlinarith only [hb,hmax,hcap,hP,hM,hg,hh,hJ,hcut,hS,hp9,hp39]

theorem pipeline_depth_bound (n : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPipeline.depth n ≤ 30*(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n)^3 := by
  have hb := (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale_bounds n).1
  have hp := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.prime_depth_bound n
  have hs := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.stage_depth_bound n
  have hp3 : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n)^3 := Nat.le_self_pow (by decide) _
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPipeline.depth
  omega





theorem need_bounds (n U : ℕ) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.need n U).word ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.envelope n*(U+1) ∧
    (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.need n U).cells ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.envelope n*(U+1) ∧
    (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.need n U).depth ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.envelope n*(U+1) := by
  have hb := (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale_bounds n).1
  have hp10 : 1 ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n)^10 := Nat.one_le_pow _ _ (by omega)
  have hmul : (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n)^10 ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n)^10*(U+1) := Nat.le_mul_of_pos_right _ (by omega)
  have hU : U ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n)^10*(U+1) := (Nat.le_succ _).trans (Nat.le_mul_of_pos_left _ hp10)
  have hp39 := Nat.pow_le_pow_right (by omega : 1 ≤ scale n) (by decide : 3 ≤ 10)
  have hp59 := Nat.pow_le_pow_right (by omega : 1 ≤ scale n) (by decide : 5 ≤ 10)
  have hp99 := Nat.pow_le_pow_right (by omega : 1 ≤ scale n) (by decide : 9 ≤ 10)
  have hw := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.pipeline_word_bound n U
  have hd := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.pipeline_depth_bound n
  rw [show _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.envelope n*(U+1)=1000000*((_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n)^10*(U+1)) by unfold _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.envelope; ring]
  change _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPipeline.word n U ≤ _ ∧ 3000*(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n)^5+U ≤ _ ∧
    _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPipeline.depth n ≤ _
  constructor
  · omega
  · constructor <;> omega

noncomputable section

theorem envelope_powerBound : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.envelope 20480 := by
  have hh := (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 1000000).mul (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale_powerBound.pow 10)
  convert hh using 1 <;> (first | rfl | norm_num)

theorem poly_need : _root_.ThreeSum1960614.Machine.Light.PolyNeed _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.need := by
  apply _root_.ThreeSum1960614.Machine.ThreeSum.PolynomialResources.polyNeed_of_envelope _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.envelope_powerBound 1
  · intro n U; simpa only [pow_one] using (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.need_bounds n U).1
  · intro n U; simpa only [pow_one] using (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.need_bounds n U).2.1
  · intro n U; simpa only [pow_one] using (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.need_bounds n U).2.2

end





end ThreeSum.EncodedColorResources

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorReportingResources

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData
set_option maxHeartbeats 1800000
set_option maxRecDepth 12000
open _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorReportingResources

section

theorem ThreeSum1960614.Machine.ThreeSum.EncodedColorReportingResources.poly_need__implementation_81192d4540 : _root_.ThreeSum1960614.Machine.Light.PolyNeed _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorReportingResources.need := by
  obtain ⟨sa,ka,ha⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.poly_need
  obtain ⟨sb,kb,hb⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupResources.poly_need
  refine ⟨sa+sb+3,ka+kb,fun n U => ?_⟩
  let F := _root_.Light.polyBound (sa+sb) (ka+kb) [n,U]
  have hA := ha n U
  have hB := hb n U
  have hma : _root_.Light.polyBound sa ka [n,U] ≤ F := _root_.ThreeSum1960614.Machine.Light.polyBound_mono (by omega) (by omega) _
  have hmb : _root_.Light.polyBound sb kb [n,U] ≤ F := _root_.ThreeSum1960614.Machine.Light.polyBound_mono (by omega) (by omega) _
  have hF : 1 ≤ F := by
    unfold F _root_.Light.polyBound
    simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]
    exact Nat.mul_pos (by positivity) (by positivity)
  have he : _root_.Light.polyBound (sa+sb+3) (ka+kb) [n,U]=8*F := by
    unfold F _root_.Light.polyBound
    rw [pow_add]
    norm_num
    ring
  rw [he]
  dsimp only [_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorReportingResources.need]
  exact ⟨by omega,by omega,by omega⟩
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.EncodedColorReportingResources.poly_need__implementation_81192d4540) := (@ThreeSum1960614.Machine.ThreeSum.EncodedColorReportingResources.poly_need__implementation_81192d4540)

#print axioms solution
