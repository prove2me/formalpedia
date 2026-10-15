-- Prove2me | solution 1 for ThreeSum.Scales.primeDepth_log_ratio_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T14:38:18.306912+00:00
-- url     : https://prove2.me/submissions/a44af1cf-e70c-481e-9449-a22e9c8f6590

import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle07
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

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









































































































































































theorem primeDepth_log_bound {n : ℕ} (hR : 4 ≤ radix n) :
    (primeDepth radix n : ℝ) * Real.log (4 * primeWindow n : ℝ) ≤
      Real.log (radix n : ℝ) := by
  have hp := primeDepth_upper radix hR
  have hpow : (4 * primeWindow n) ^ primeDepth radix n ≤ radix n := by omega
  have hpos : (0 : ℝ) < ((4 * primeWindow n : ℕ) : ℝ) ^ primeDepth radix n := by
    have hy := primeWindow_ge_two n
    positivity
  have hpowR : ((4 * primeWindow n : ℕ) : ℝ) ^ primeDepth radix n ≤ (radix n : ℝ) := by
    exact_mod_cast hpow
  have hl := Real.log_le_log hpos hpowR
  simpa only [Nat.cast_mul, Nat.cast_ofNat, Real.log_pow] using hl

theorem primeBase_log_tendsto_atTop :
    Tendsto (fun n : ℕ => Real.log (4 * primeWindow n : ℝ)) atTop atTop := by
  have hy := (tendsto_natCast_atTop_atTop (R := ℝ)).comp primeWindow_tendsto_atTop
  exact Real.tendsto_log_atTop.comp (hy.const_mul_atTop (by norm_num : (0 : ℝ) < 4))

theorem primeDepth_log_ratio_tendsto_zero_sourceProof :
    Tendsto (fun n : ℕ => (primeDepth radix n : ℝ) / Real.log n) atTop (𝓝 0) := by
  have hupper := radix_log_ratio_tendsto.mul primeBase_log_tendsto_atTop.inv_tendsto_atTop
  simp only [mul_zero] at hupper
  apply squeeze_zero' _ _ hupper
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    exact div_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast hn))
  · filter_upwards [radix_eventually_ge_four, eventually_ge_atTop (2 : ℕ)] with n hR hn
    have hy := primeWindow_ge_two n
    have hb : (0 : ℝ) < Real.log (4 * primeWindow n : ℝ) :=
      Real.log_pos (by exact_mod_cast (by omega : 1 < 4 * primeWindow n))
    have hlog : (0 : ℝ) < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    have hdepth := (le_div_iff₀ hb).mpr (primeDepth_log_bound hR)
    have hd := div_le_div_of_nonneg_right hdepth hlog.le
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, Pi.inv_apply] using hd


































































































































































































































































































































end

end ThreeSum.Scales

end


theorem solution : @Filter.Tendsto.{0, 0} Nat Real
  (fun (n : Nat) =>
    @HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (ThreeSum.Scales.primeDepth ThreeSum.Scales.radix n))
      (Real.log (@Nat.cast.{0} Real Real.instNatCast n)))
  (@Filter.atTop.{0} Nat Nat.instPreorder)
  (@nhds.{0} Real
    (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))) := by
  exact @ThreeSum.Scales.primeDepth_log_ratio_tendsto_zero_sourceProof

#print axioms solution
