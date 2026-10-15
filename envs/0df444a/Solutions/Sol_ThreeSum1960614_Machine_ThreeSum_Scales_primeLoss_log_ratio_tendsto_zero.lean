-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.Scales.primeLoss_log_ratio_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T09:10:21.864601+00:00
-- url     : https://prove2.me/submissions/4b91da99-3f8f-4079-bac9-d6337e6e006c

import Definitions.Def_ThreeSum1960614_Analysis
import Definitions.Def_ThreeSum1960614_Machine_Bundle001
import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Definitions.Def_ThreeSum1960614_Machine_Bundle004
import Definitions.Def_ThreeSum1960614_Machine_Bundle005
import Definitions.Def_ThreeSum1960614_Machine_Bundle006
import Definitions.Def_ThreeSum1960614_Machine_Bundle007
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle07
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_Scales_primeDepth_log_ratio_tendsto_zero
import Theorems.Thm_ThreeSum_Scales_natSqrt_ratio_tendsto_zero

local instance platformRadixNonzero_5d60ae9653 (n : ℕ) : NeZero (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) :=
  ⟨Nat.ne_of_gt (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix_pos n)⟩


namespace Filter
end Filter
namespace Real
end Real
namespace ThreeSum
end ThreeSum
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.Scales
end ThreeSum1960614.Machine.ThreeSum.Scales

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













































































end

end ThreeSum.Scales

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales

open _root_.Filter
open _root_.Real
open scoped _root_.Topology
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales

section

theorem ThreeSum1960614.Machine.ThreeSum.Scales.primeLoss_log_ratio_tendsto_zero__implementation_bf1790d91b :
    Tendsto (fun n : ℕ => Real.log (_root_.ThreeSum.Scales.primeLoss _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n : ℝ) / Real.log n) atTop (𝓝 0) := by
  have hc := _root_.ThreeSum.Asymptotics.log_nat_tendsto_atTop.inv_tendsto_atTop.const_mul (Real.log 32)
  have hd := _root_.ThreeSum1960614.Machine.ThreeSum.Scales.primeDepth_log_ratio_tendsto_zero.const_mul (Real.log 4)
  have h := (hc.add _root_.ThreeSum1960614.Machine.ThreeSum.Scales.primeWindow_log_ratio_tendsto_zero).add hd
  simp only [mul_zero, zero_add, add_zero] at h
  apply h.congr'
  filter_upwards [] with n
  have hy : (_root_.ThreeSum.Scales.primeWindow n : ℝ) ≠ 0 := by exact_mod_cast (by have := _root_.ThreeSum.Scales.primeWindow_ge_two n; omega : primeWindow n ≠ 0)
  simp only [_root_.ThreeSum.Scales.primeLoss, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [Real.log_mul (mul_ne_zero (by norm_num) hy) (by positivity),
    Real.log_mul (by norm_num : (32 : ℝ) ≠ 0) hy, Real.log_pow]
  simp only [add_div, Pi.inv_apply]
  ring
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.Scales.primeLoss_log_ratio_tendsto_zero__implementation_bf1790d91b) := (@ThreeSum1960614.Machine.ThreeSum.Scales.primeLoss_log_ratio_tendsto_zero__implementation_bf1790d91b)

#print axioms solution
