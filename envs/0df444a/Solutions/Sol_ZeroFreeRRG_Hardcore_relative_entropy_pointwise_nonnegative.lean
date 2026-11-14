-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.relative_entropy_pointwise_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T06:40:33.757118+00:00
-- url     : https://prove2.me/submissions/523ac56d-5e00-4f1f-a0db-826d9cc57f14

import Mathlib
set_option autoImplicit false

/-- The pointwise relative-entropy gap is nonnegative. -/
theorem solution (p q : ℝ) (hp : 0 ≤ p) (hq : 0 < q) :
    0 ≤ p * Real.log p - p * Real.log q - p + q := by
  by_cases hp0 : p = 0
  · simp [hp0, le_of_lt hq]
  · have hp' : 0 < p := lt_of_le_of_ne hp (Ne.symm hp0)
    have hdiv : 0 ≤ p/q := div_nonneg hp hq.le
    have hbase := Real.self_sub_one_le_mul_log hdiv
    have hh := mul_le_mul_of_nonneg_left hbase hq.le
    rw [Real.log_div hp0 (ne_of_gt hq)] at hh
    have hqn : q ≠ 0 := ne_of_gt hq
    have hc : q * (p/q) = p := by field_simp
    nlinarith [hh]
