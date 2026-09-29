-- Prove2me | solution 1 for TaoFivePrimes.typeII_log_integral
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-09-14T04:51:59.283866+00:00
-- url     : https://prove2.me/submissions/7bc5d063-6e7f-4254-b915-fe77e36d3f20

import Mathlib

open MeasureTheory intervalIntegral

section PartS5II
open MeasureTheory intervalIntegral
namespace TaoS5II

theorem hasDerivAt_log_sq {W : ℝ} (hW : 0 < W) :
    HasDerivAt (fun t : ℝ => Real.log t ^ 2 / 2) (Real.log W / W) W := by
  have h1 : HasDerivAt Real.log W⁻¹ W := Real.hasDerivAt_log (ne_of_gt hW)
  have h2 : HasDerivAt (fun t : ℝ => Real.log t * Real.log t)
      (W⁻¹ * Real.log W + Real.log W * W⁻¹) W := h1.mul h1
  have h3 : HasDerivAt (fun t : ℝ => Real.log t * Real.log t / 2)
      ((W⁻¹ * Real.log W + Real.log W * W⁻¹) / 2) W := h2.div_const 2
  have hW0 : W ≠ 0 := ne_of_gt hW
  have heq : (W⁻¹ * Real.log W + Real.log W * W⁻¹) / 2 = Real.log W / W := by
    field_simp
    ring
  rw [heq] at h3
  have hfun : (fun t : ℝ => Real.log t ^ 2 / 2) = fun t : ℝ => Real.log t * Real.log t / 2 := by
    funext t; ring
  rw [hfun]
  exact h3

/-- **Tao, Section 5**: the logarithmic integral appearing in the Type II estimate. -/
theorem log_div_integral (b c : ℝ) (hb : 0 < b) (hbc : b ≤ c) :
    4 * (∫ W in b..c, Real.log W / W)
      = 2 * Real.log (c / b) * Real.log (c * b) := by
  have hc : 0 < c := lt_of_lt_of_le hb hbc
  have hderiv : ∀ t ∈ Set.uIcc b c, HasDerivAt (fun s : ℝ => Real.log s ^ 2 / 2)
      (Real.log t / t) t := by
    intro t ht
    rw [Set.uIcc_of_le hbc, Set.mem_Icc] at ht
    exact hasDerivAt_log_sq (lt_of_lt_of_le hb ht.1)
  have hint : IntervalIntegrable (fun t : ℝ => Real.log t / t) MeasureTheory.volume b c := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hbc]
    intro t ht
    rw [Set.mem_Icc] at ht
    have ht0 : t ≠ 0 := ne_of_gt (lt_of_lt_of_le hb ht.1)
    exact ((Real.continuousOn_log.continuousAt
      (by simpa using ht0)).div continuousAt_id ht0).continuousWithinAt
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [hFTC]
  have hlogdiv : Real.log (c / b) = Real.log c - Real.log b :=
    Real.log_div (ne_of_gt hc) (ne_of_gt hb)
  have hlogmul : Real.log (c * b) = Real.log c + Real.log b :=
    Real.log_mul (ne_of_gt hc) (ne_of_gt hb)
  rw [hlogdiv, hlogmul]
  ring

end TaoS5II
end PartS5II

theorem solution (b c : ℝ) (hb : 0 < b) (hbc : b ≤ c) :
    4 * (∫ W in b..c, Real.log W / W) = 2 * Real.log (c / b) * Real.log (c * b) :=
  TaoS5II.log_div_integral b c hb hbc
