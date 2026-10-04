-- Prove2me | solution 1 for TaoFivePrimes.eta0_deriv_L1_eq_eight_log_two
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-09-13T21:14:32.930517+00:00
-- url     : https://prove2.me/submissions/a32dfa4e-388a-4479-bac8-95e7c3c55ffb

import Mathlib
import Definitions.Def_TaoFivePrimes_RepresentationCount

open MeasureTheory
open TaoFivePrimes

namespace TaoS13

theorem eta0_eq_zero_of_le {t : ℝ} (h : t ≤ 1/4) : eta0 t = 0 := by
  unfold eta0
  by_cases ht : 0 < t
  · rw [if_pos ht, max_eq_left, mul_zero]
    have h2 : Real.log (2*t) ≤ Real.log (1/2) := Real.log_le_log (by linarith) (by linarith)
    have h3 : Real.log (1/2 : ℝ) = -Real.log 2 := by
      rw [show (1/2 : ℝ) = (2:ℝ)⁻¹ by norm_num, Real.log_inv]
    rw [h3] at h2
    linarith [neg_le_abs (Real.log (2*t))]
  · rw [if_neg ht]

theorem eta0_eq_zero_of_ge {t : ℝ} (h : 1 ≤ t) : eta0 t = 0 := by
  unfold eta0
  have ht : 0 < t := by linarith
  rw [if_pos ht, max_eq_left, mul_zero]
  have h2 : Real.log 2 ≤ Real.log (2*t) := Real.log_le_log (by norm_num) (by linarith)
  linarith [le_abs_self (Real.log (2*t))]

theorem eta0_on_left {t : ℝ} (h1 : 1/4 ≤ t) (h2 : t ≤ 1/2) :
    eta0 t = 4 * (2 * Real.log 2 + Real.log t) := by
  have ht : 0 < t := by linarith
  have hlog : Real.log (2*t) = Real.log 2 + Real.log t :=
    Real.log_mul (by norm_num) (ne_of_gt ht)
  have hle : Real.log (2*t) ≤ 0 := by
    rw [show (0:ℝ) = Real.log 1 by simp]
    exact Real.log_le_log (by linarith) (by linarith)
  have hge : (0:ℝ) ≤ 2 * Real.log 2 + Real.log t := by
    have h : Real.log (1/4 : ℝ) ≤ Real.log t := Real.log_le_log (by norm_num) h1
    have h4 : Real.log (1/4 : ℝ) = -(2 * Real.log 2) := by
      rw [show (1/4 : ℝ) = (2:ℝ)⁻¹ ^ 2 by norm_num, Real.log_pow, Real.log_inv]
      push_cast; ring
    linarith [h4 ▸ h]
  unfold eta0
  rw [if_pos ht, abs_of_nonpos hle, hlog, max_eq_right (by linarith)]
  ring

theorem eta0_on_right {t : ℝ} (h1 : 1/2 ≤ t) (h2 : t ≤ 1) :
    eta0 t = -4 * Real.log t := by
  have ht : 0 < t := by linarith
  have hlog : Real.log (2*t) = Real.log 2 + Real.log t :=
    Real.log_mul (by norm_num) (ne_of_gt ht)
  have hge : (0:ℝ) ≤ Real.log (2*t) := by
    rw [show (0:ℝ) = Real.log 1 by simp]
    exact Real.log_le_log (by norm_num) (by linarith)
  have hlt : Real.log t ≤ 0 := by
    rw [show (0:ℝ) = Real.log 1 by simp]
    exact Real.log_le_log ht h2
  unfold eta0
  rw [if_pos ht, abs_of_nonneg hge, hlog, max_eq_right (by linarith)]
  ring

theorem deriv_lo {t : ℝ} (h : t < 1/4) : deriv eta0 t = 0 := by
  have hev : eta0 =ᶠ[nhds t] (fun _ => (0:ℝ)) := by
    filter_upwards [Iio_mem_nhds h] with u hu
    exact eta0_eq_zero_of_le (le_of_lt hu)
  rw [hev.deriv_eq, deriv_const]

theorem deriv_hi {t : ℝ} (h : 1 < t) : deriv eta0 t = 0 := by
  have hev : eta0 =ᶠ[nhds t] (fun _ => (0:ℝ)) := by
    filter_upwards [Ioi_mem_nhds h] with u hu
    exact eta0_eq_zero_of_ge (le_of_lt hu)
  rw [hev.deriv_eq, deriv_const]

theorem deriv_left {t : ℝ} (h1 : 1/4 < t) (h2 : t < 1/2) : deriv eta0 t = 4 / t := by
  have hev : eta0 =ᶠ[nhds t] (fun u => 4 * (2 * Real.log 2 + Real.log u)) := by
    filter_upwards [Ioo_mem_nhds h1 h2] with u hu
    exact eta0_on_left (le_of_lt hu.1) (le_of_lt hu.2)
  rw [hev.deriv_eq]
  have hd : HasDerivAt (fun u : ℝ => 4 * (2 * Real.log 2 + Real.log u)) (4 * t⁻¹) t :=
    ((Real.hasDerivAt_log (by linarith : t ≠ 0)).const_add (2 * Real.log 2)).const_mul 4
  rw [hd.deriv]
  field_simp

theorem deriv_right {t : ℝ} (h1 : 1/2 < t) (h2 : t < 1) : deriv eta0 t = -4 / t := by
  have hev : eta0 =ᶠ[nhds t] (fun u => -4 * Real.log u) := by
    filter_upwards [Ioo_mem_nhds h1 h2] with u hu
    exact eta0_on_right (le_of_lt hu.1) (le_of_lt hu.2)
  rw [hev.deriv_eq]
  have hd : HasDerivAt (fun u : ℝ => -4 * Real.log u) (-4 * t⁻¹) t :=
    (Real.hasDerivAt_log (by linarith : t ≠ 0)).const_mul (-4)
  rw [hd.deriv]
  field_simp

/-- **Tao, equation (s1-3).**  `‖η₀'‖_{L¹(ℝ)} = 8 log 2`. -/
theorem eta0_deriv_L1 : ∫ t : ℝ, |deriv eta0 t| = 8 * Real.log 2 := by
  have hcompl : ∀ t ∈ (Set.Icc (1/4:ℝ) 1)ᶜ, |deriv eta0 t| = 0 := by
    intro t ht
    simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le] at ht
    rcases ht with h | h
    · rw [deriv_lo h, abs_zero]
    · rw [deriv_hi h, abs_zero]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hcompl,
    MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (1/4:ℝ) ≤ 1)]
  have hnull : (volume ({(1/2:ℝ), 1} : Set ℝ)) = 0 :=
    measure_union_null (measure_singleton _) (measure_singleton _)
  have hae : ∀ᵐ t, t ∈ Set.uIoc (1/4:ℝ) 1 → |deriv eta0 t| = 4 / t := by
    filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr hnull] with t ht hmem
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
      not_or] at ht
    rw [Set.uIoc_of_le (by norm_num : (1/4:ℝ) ≤ 1), Set.mem_Ioc] at hmem
    have ht0 : (0:ℝ) < t := by linarith [hmem.1]
    rcases lt_or_gt_of_ne ht.1 with h | h
    · rw [deriv_left hmem.1 h, abs_of_nonneg (by positivity)]
    · rw [deriv_right h (lt_of_le_of_ne hmem.2 ht.2), abs_of_nonpos (by
        rw [neg_div]; simp only [neg_nonpos]; positivity)]
      rw [neg_div, neg_neg]
  rw [intervalIntegral.integral_congr_ae hae]
  have h4 : ∀ t : ℝ, (4:ℝ) / t = 4 * t⁻¹ := fun t => by ring
  simp only [h4]
  rw [intervalIntegral.integral_const_mul, integral_inv (by
    rw [Set.uIcc_of_le (by norm_num : (1/4:ℝ) ≤ 1)]
    simp only [Set.mem_Icc, not_and_or, not_le]
    left; norm_num)]
  rw [show (1:ℝ) / (1/4) = 4 by norm_num, show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  push_cast; ring

end TaoS13

theorem solution : (∫ t : ℝ, |deriv TaoFivePrimes.eta0 t|) = 8 * Real.log 2 :=
  TaoS13.eta0_deriv_L1
