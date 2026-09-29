-- Prove2me | solution 1 for TaoFivePrimes.two_norm_le_abs_sin_le_pi_norm
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-09-13T21:54:04.491225+00:00
-- url     : https://prove2.me/submissions/daf954d0-374d-4adc-b6c5-05968beaea55

import Mathlib

namespace TaoSinx

/-- **Tao, equation (2.1).**  `2‖α‖_{ℝ/ℤ} ≤ |sin πα| ≤ π‖α‖_{ℝ/ℤ} ≤ |tan πα|`,
with `‖α‖_{ℝ/ℤ}` the distance from `α` to the nearest integer. -/
theorem sinx (alpha : ℝ) :
    2 * |alpha - round alpha| ≤ |Real.sin (Real.pi * alpha)|
      ∧ |Real.sin (Real.pi * alpha)| ≤ Real.pi * |alpha - round alpha|
      ∧ (|alpha - round alpha| < 1/2 →
          Real.pi * |alpha - round alpha| ≤ |Real.tan (Real.pi * alpha)|) := by
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  set r : ℤ := round alpha with hr
  set t : ℝ := alpha - r with ht
  have htb : |t| ≤ 1/2 := abs_sub_round alpha
  have hdec : Real.pi * alpha = Real.pi * t + r * Real.pi := by rw [ht]; ring
  have hsign : |((-1 : ℝ) ^ r)| = 1 := by rw [abs_zpow]; norm_num
  have habs : |Real.sin (Real.pi * alpha)| = Real.sin (Real.pi * |t|) := by
    rw [hdec, Real.sin_add_int_mul_pi, abs_mul, hsign, one_mul]
    rcases abs_cases t with ⟨he, _⟩ | ⟨he, _⟩
    · rw [he, abs_of_nonneg]
      exact Real.sin_nonneg_of_nonneg_of_le_pi (by nlinarith [he, htb]) (by nlinarith [he, htb])
    · rw [he]
      have hnn : 0 ≤ Real.sin (Real.pi * -t) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by nlinarith [he, htb]) (by nlinarith [he, htb])
      have heq : Real.sin (Real.pi * t) = - Real.sin (Real.pi * -t) := by
        rw [show Real.pi * -t = -(Real.pi * t) by ring, Real.sin_neg, neg_neg]
      rw [heq, abs_neg, abs_of_nonneg hnn]
  have hbound : Real.pi * |t| ≤ Real.pi / 2 := by nlinarith [htb, abs_nonneg t]
  refine ⟨?_, ?_, ?_⟩
  · rw [habs]
    have hj := Real.mul_le_sin (x := Real.pi * |t|) (by positivity) hbound
    calc 2 * |t| = 2 / Real.pi * (Real.pi * |t|) := by field_simp
      _ ≤ Real.sin (Real.pi * |t|) := hj
  · rw [habs]
    exact Real.sin_le (by positivity)
  · intro hlt
    have htan : Real.tan (Real.pi * alpha) = Real.tan (Real.pi * t) := by
      rw [hdec]
      exact (Real.tan_periodic.int_mul r) (Real.pi * t)
    rw [htan]
    rcases lt_trichotomy t 0 with hneg | hzero | hpos
    · have habs' : |t| = -t := abs_of_neg hneg
      have h1 : (0:ℝ) < Real.pi * (-t) := by nlinarith
      have h2 : Real.pi * (-t) < Real.pi / 2 := by
        rw [habs'] at hlt; nlinarith
      have := Real.lt_tan h1 h2
      have hodd : Real.tan (Real.pi * t) = - Real.tan (Real.pi * (-t)) := by
        rw [show Real.pi * (-t) = -(Real.pi * t) by ring, Real.tan_neg, neg_neg]
      rw [hodd, abs_neg, habs']
      calc Real.pi * -t ≤ Real.tan (Real.pi * -t) := le_of_lt this
        _ ≤ |Real.tan (Real.pi * -t)| := le_abs_self _
    · rw [hzero]
      simp
    · have habs' : |t| = t := abs_of_pos hpos
      have h1 : (0:ℝ) < Real.pi * t := by nlinarith
      have h2 : Real.pi * t < Real.pi / 2 := by
        rw [habs'] at hlt; nlinarith
      have := Real.lt_tan h1 h2
      rw [habs']
      calc Real.pi * t ≤ Real.tan (Real.pi * t) := le_of_lt this
        _ ≤ |Real.tan (Real.pi * t)| := le_abs_self _

end TaoSinx

theorem solution (alpha : ℝ) :
    2 * |alpha - round alpha| ≤ |Real.sin (Real.pi * alpha)|
      ∧ |Real.sin (Real.pi * alpha)| ≤ Real.pi * |alpha - round alpha|
      ∧ (|alpha - round alpha| < 1/2 →
          Real.pi * |alpha - round alpha| ≤ |Real.tan (Real.pi * alpha)|) :=
  TaoSinx.sinx alpha
