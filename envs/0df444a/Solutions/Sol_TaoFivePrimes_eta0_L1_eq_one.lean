-- Prove2me | solution 1 for TaoFivePrimes.eta0_L1_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-09-13T21:07:34.58088+00:00
-- url     : https://prove2.me/submissions/2d1ec562-9682-44db-afc9-409fb87f20d4

import Mathlib
import Definitions.Def_TaoFivePrimes_RepresentationCount

open MeasureTheory Real intervalIntegral
open TaoFivePrimes

namespace TaoEta0

theorem eta0_nonneg (t : ℝ) : 0 ≤ eta0 t := by
  unfold eta0; split
  · positivity
  · exact le_rfl

theorem eta0_eq_zero_of_le (t : ℝ) (h : t ≤ 1/4) : eta0 t = 0 := by
  unfold eta0
  by_cases ht : 0 < t
  · rw [if_pos ht, max_eq_left, mul_zero]
    have h2 : Real.log (2*t) ≤ Real.log (1/2) := by
      refine Real.log_le_log (by linarith) (by linarith)
    have h3 : Real.log (1/2 : ℝ) = -Real.log 2 := by
      rw [show (1/2 : ℝ) = 2⁻¹ by norm_num, Real.log_inv]
    rw [h3] at h2
    linarith [neg_le_abs (Real.log (2*t))]
  · rw [if_neg ht]

theorem eta0_eq_zero_of_ge (t : ℝ) (h : 1 ≤ t) : eta0 t = 0 := by
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
    have : Real.log (1/4 : ℝ) ≤ Real.log t := Real.log_le_log (by norm_num) h1
    have h4 : Real.log (1/4 : ℝ) = -(2 * Real.log 2) := by
      rw [show (1/4 : ℝ) = (2:ℝ)⁻¹ ^ 2 by norm_num, Real.log_pow, Real.log_inv]
      push_cast; ring
    linarith [h4 ▸ this]
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

theorem contOn_left : ContinuousOn eta0 (Set.uIcc (1/4:ℝ) (1/2)) := by
  refine ContinuousOn.congr (f := fun t => 4 * (2 * Real.log 2 + Real.log t)) ?_ ?_
  · refine continuousOn_const.mul (continuousOn_const.add ?_)
    refine Real.continuousOn_log.mono ?_
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (1/4:ℝ) ≤ 1/2), Set.mem_Icc] at ht
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h; rw [h] at ht; linarith [ht.1]
  · intro t ht
    rw [Set.uIcc_of_le (by norm_num : (1/4:ℝ) ≤ 1/2), Set.mem_Icc] at ht
    exact eta0_on_left ht.1 ht.2

theorem contOn_right : ContinuousOn eta0 (Set.uIcc (1/2:ℝ) 1) := by
  refine ContinuousOn.congr (f := fun t => -4 * Real.log t) ?_ ?_
  · refine continuousOn_const.mul ?_
    refine Real.continuousOn_log.mono ?_
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (1/2:ℝ) ≤ 1), Set.mem_Icc] at ht
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h; rw [h] at ht; linarith [ht.1]
  · intro t ht
    rw [Set.uIcc_of_le (by norm_num : (1/2:ℝ) ≤ 1), Set.mem_Icc] at ht
    exact eta0_on_right ht.1 ht.2

/-- **Tao, equation (s1).**  `‖η₀‖_{L¹(ℝ)} = 1`: the logarithmic cutoff has unit mass. -/
theorem eta0_integral : ∫ t : ℝ, eta0 t = 1 := by
  have hzero : ∀ t ∈ (Set.Ioc (1/4:ℝ) 1)ᶜ, eta0 t = 0 := by
    intro t ht
    simp only [Set.mem_compl_iff, Set.mem_Ioc, not_and_or, not_lt, not_le] at ht
    rcases ht with h | h
    · exact eta0_eq_zero_of_le t h
    · exact eta0_eq_zero_of_ge t (le_of_lt h)
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero,
    ← intervalIntegral.integral_of_le (by norm_num : (1/4:ℝ) ≤ 1),
    ← intervalIntegral.integral_add_adjacent_intervals
      (b := (1/2 : ℝ)) (contOn_left.intervalIntegrable) (contOn_right.intervalIntegrable)]
  have hL : ∫ t in (1/4:ℝ)..(1/2), eta0 t
      = ∫ t in (1/4:ℝ)..(1/2), (4 * (2 * Real.log 2 + Real.log t)) := by
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [Set.uIcc_of_le (by norm_num : (1/4:ℝ) ≤ 1/2), Set.mem_Icc] at ht
    exact eta0_on_left ht.1 ht.2
  have hR : ∫ t in (1/2:ℝ)..1, eta0 t = ∫ t in (1/2:ℝ)..1, (-4 * Real.log t) := by
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [Set.uIcc_of_le (by norm_num : (1/2:ℝ) ≤ 1), Set.mem_Icc] at ht
    exact eta0_on_right ht.1 ht.2
  rw [hL, hR]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (intervalIntegrable_const)
      (intervalIntegral.intervalIntegrable_log (by norm_num)),
    integral_log, integral_log, intervalIntegral.integral_const]
  have h2 : Real.log (1/2 : ℝ) = -Real.log 2 := by
    rw [show (1/2 : ℝ) = (2:ℝ)⁻¹ by norm_num, Real.log_inv]
  have h4 : Real.log (1/4 : ℝ) = -(2 * Real.log 2) := by
    rw [show (1/4 : ℝ) = (2:ℝ)⁻¹ ^ 2 by norm_num, Real.log_pow, Real.log_inv]
    push_cast; ring
  rw [h2, h4, Real.log_one]
  ring

end TaoEta0

theorem solution : (∫ t : ℝ, TaoFivePrimes.eta0 t) = 1 := TaoEta0.eta0_integral
