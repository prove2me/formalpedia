-- Prove2me | solution 1 for ThreeSum.Scales.scoreLoss_log_ratio_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:00:06.84621+00:00
-- url     : https://prove2.me/submissions/b5176037-1fdd-4dbf-aa26-439c4cd827a0

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

























































































































































theorem log_bits_over_windowExponent_tendsto_zero :
    Tendsto (fun m : ℕ => Real.log (m + 1 : ℝ) / windowExponent m) atTop (𝓝 0) := by
  have ht := (tendsto_natCast_atTop_atTop (R := ℝ)).comp windowExponent_tendsto_atTop
  have hu := (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp ht).const_mul 2
  simp only [mul_zero] at hu
  apply squeeze_zero' _ _ hu
  · exact Filter.Eventually.of_forall (fun m =>
      div_nonneg (Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) m; linarith))
        (Nat.cast_nonneg _))
  · filter_upwards [] with m
    have hs : (m + 1 : ℝ) ≤ (windowExponent m : ℝ) ^ 2 := by
      exact_mod_cast bits_add_one_le_windowExponent_sq m
    have hlog := Real.log_le_log (by positivity : (0 : ℝ) < m + 1) hs
    rw [Real.log_pow] at hlog
    have hd := div_le_div_of_nonneg_right hlog (Nat.cast_nonneg (α := ℝ) (windowExponent m))
    simpa only [Function.comp_def, id_eq, Nat.cast_ofNat, mul_div_assoc] using hd

theorem log_bits_over_primeBase_tendsto_zero :
    Tendsto (fun n : ℕ => Real.log (inputBits n + 1 : ℝ) /
      Real.log (4 * primeWindow n : ℝ)) atTop (𝓝 0) := by
  have hu := (log_bits_over_windowExponent_tendsto_zero.comp inputBits_tendsto_atTop).div_const
    (Real.log 2)
  simp only [zero_div] at hu
  apply squeeze_zero' _ _ hu
  · filter_upwards [] with n
    have hy := primeWindow_ge_two n
    have hb : 0 ≤ Real.log (4 * primeWindow n : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ 4 * primeWindow n))
    have hn : 0 ≤ Real.log (inputBits n + 1 : ℝ) :=
      Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) (inputBits n); linarith)
    exact div_nonneg hn hb
  · filter_upwards [] with n
    have hy := primeWindow_ge_two n
    have hypo : (0 : ℝ) < primeWindow n := by exact_mod_cast (by omega : 0 < primeWindow n)
    have hly : 0 < Real.log (primeWindow n : ℝ) :=
      Real.log_pos (by exact_mod_cast (by omega : 1 < primeWindow n))
    have hlyb : Real.log (primeWindow n : ℝ) ≤ Real.log (4 * primeWindow n : ℝ) :=
      Real.log_le_log hypo (by linarith)
    have hn : 0 ≤ Real.log (inputBits n + 1 : ℝ) :=
      Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) (inputBits n); linarith)
    have hd := div_le_div_of_nonneg_left hn hly hlyb
    simpa only [Function.comp_def, primeWindow, Nat.cast_pow, Nat.cast_ofNat,
      Real.log_pow, div_div] using hd

theorem scoreBase_log_over_primeBase_tendsto_zero (k : ℕ) :
    Tendsto (fun n : ℕ => Real.log (16 * ((k : ℝ) + 2) * (inputBits n + 1)) /
      Real.log (4 * primeWindow n : ℝ)) atTop (𝓝 0) := by
  have hc := primeBase_log_tendsto_atTop.inv_tendsto_atTop.const_mul
    (Real.log (16 * ((k : ℝ) + 2)))
  have h := hc.add log_bits_over_primeBase_tendsto_zero
  simp only [mul_zero, zero_add] at h
  apply h.congr'
  filter_upwards [] with n
  rw [Real.log_mul (by positivity : (16 * ((k : ℝ) + 2)) ≠ 0)
    (by positivity : (inputBits n + 1 : ℝ) ≠ 0)]
  simp only [Pi.inv_apply, add_div]
  ring

theorem scoreLoss_log_ratio_tendsto_zero_sourceProof (k : ℕ) :
    Tendsto (fun n : ℕ => Real.log (scoreLoss k n : ℝ) / Real.log n) atTop (𝓝 0) := by
  have hu := radix_log_ratio_tendsto.mul (scoreBase_log_over_primeBase_tendsto_zero k)
  simp only [mul_zero] at hu
  apply squeeze_zero' _ _ hu
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    exact div_nonneg (Real.log_natCast_nonneg _) (Real.log_nonneg (by exact_mod_cast hn))
  · filter_upwards [radix_eventually_ge_four, eventually_ge_atTop (2 : ℕ)] with n hR hn
    have hy := primeWindow_ge_two n
    have hb : 0 < Real.log (4 * primeWindow n : ℝ) :=
      Real.log_pos (by exact_mod_cast (by omega : 1 < 4 * primeWindow n))
    have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    have hs : 0 ≤ Real.log (16 * ((k : ℝ) + 2) * (inputBits n + 1)) := by
      apply Real.log_nonneg
      have hk := Nat.cast_nonneg (α := ℝ) k
      have hm := Nat.cast_nonneg (α := ℝ) (inputBits n)
      nlinarith
    have hd := (le_div_iff₀ hb).mpr (primeDepth_log_bound hR)
    have hmul := mul_le_mul_of_nonneg_right hd hs
    have hdiv := div_le_div_of_nonneg_right hmul hlog.le
    simp only [scoreLoss, Nat.cast_pow, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat,
      Nat.cast_one, Real.log_pow]
    apply le_of_le_of_eq hdiv
    ring







































































































end

end ThreeSum.Scales

end


theorem solution : ∀ (k : Nat),
  @Filter.Tendsto.{0, 0} Nat Real
    (fun (n : Nat) =>
      @HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (Real.log (@Nat.cast.{0} Real Real.instNatCast (ThreeSum.Scales.scoreLoss k n)))
        (Real.log (@Nat.cast.{0} Real Real.instNatCast n)))
    (@Filter.atTop.{0} Nat Nat.instPreorder)
    (@nhds.{0} Real
      (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))) := by
  exact @ThreeSum.Scales.scoreLoss_log_ratio_tendsto_zero_sourceProof

#print axioms solution
