-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.Scales.primeDepth_log_ratio_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T05:32:40.464258+00:00
-- url     : https://prove2.me/submissions/1c62e4d4-2e2f-467a-90f4-d25930d0e3a6

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

































































theorem primeDepth_upper (R : ℕ → ℕ) {n : ℕ} (hR : 4 ≤ R n) :
    4 * (4 * _root_.ThreeSum.Scales.primeWindow n) ^ _root_.ThreeSum.Scales.primeDepth R n ≤ R n := by
  have hr : R n / 4 ≠ 0 := by omega
  have h := Nat.pow_log_le_self (4 * _root_.ThreeSum.Scales.primeWindow n) hr
  have h4 := Nat.mul_le_mul_left 4 h
  have hd := Nat.div_mul_le_self (R n) 4
  simpa [_root_.ThreeSum.Scales.primeDepth, Nat.mul_comm] using h4.trans (by simpa [Nat.mul_comm] using hd)

























theorem primeDepth_log_bound {n : ℕ} (hR : 4 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) :
    (_root_.ThreeSum.Scales.primeDepth _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n : ℝ) * Real.log (4 * _root_.ThreeSum.Scales.primeWindow n : ℝ) ≤
      Real.log (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n : ℝ) := by
  have hp := _root_.ThreeSum1960614.Machine.ThreeSum.Scales.primeDepth_upper _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix hR
  have hpow : (4 * _root_.ThreeSum.Scales.primeWindow n) ^ _root_.ThreeSum.Scales.primeDepth _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n ≤ _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n := by omega
  have hpos : (0 : ℝ) < ((4 * _root_.ThreeSum.Scales.primeWindow n : ℕ) : ℝ) ^ _root_.ThreeSum.Scales.primeDepth _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n := by
    have hy := _root_.ThreeSum.Scales.primeWindow_ge_two n
    positivity
  have hpowR : ((4 * _root_.ThreeSum.Scales.primeWindow n : ℕ) : ℝ) ^ _root_.ThreeSum.Scales.primeDepth _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n : ℝ) := by
    exact_mod_cast hpow
  have hl := Real.log_le_log hpos hpowR
  simpa only [Nat.cast_mul, Nat.cast_ofNat, Real.log_pow] using hl

theorem primeBase_log_tendsto_atTop :
    Tendsto (fun n : ℕ => Real.log (4 * _root_.ThreeSum.Scales.primeWindow n : ℝ)) atTop atTop := by
  have hy := (tendsto_natCast_atTop_atTop (R := ℝ)).comp _root_.ThreeSum.Scales.primeWindow_tendsto_atTop
  exact Real.tendsto_log_atTop.comp (hy.const_mul_atTop (by norm_num : (0 : ℝ) < 4))









































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

theorem ThreeSum1960614.Machine.ThreeSum.Scales.primeDepth_log_ratio_tendsto_zero__implementation_cb68b46298 :
    Tendsto (fun n : ℕ => (_root_.ThreeSum.Scales.primeDepth _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n : ℝ) / Real.log n) atTop (𝓝 0) := by
  have hupper := _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix_log_ratio_tendsto.mul _root_.ThreeSum1960614.Machine.ThreeSum.Scales.primeBase_log_tendsto_atTop.inv_tendsto_atTop
  simp only [mul_zero] at hupper
  apply squeeze_zero' _ _ hupper
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    exact div_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast hn))
  · filter_upwards [_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix_eventually_ge_four, eventually_ge_atTop (2 : ℕ)] with n hR hn
    have hy := _root_.ThreeSum.Scales.primeWindow_ge_two n
    have hb : (0 : ℝ) < Real.log (4 * _root_.ThreeSum.Scales.primeWindow n : ℝ) :=
      Real.log_pos (by exact_mod_cast (by omega : 1 < 4 * primeWindow n))
    have hlog : (0 : ℝ) < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    have hdepth := (le_div_iff₀ hb).mpr (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.primeDepth_log_bound hR)
    have hd := div_le_div_of_nonneg_right hdepth hlog.le
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, Pi.inv_apply] using hd
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.Scales.primeDepth_log_ratio_tendsto_zero__implementation_cb68b46298) := (@ThreeSum1960614.Machine.ThreeSum.Scales.primeDepth_log_ratio_tendsto_zero__implementation_cb68b46298)

#print axioms solution
