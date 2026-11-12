-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakenext100.P45.logSumBounds
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-11T19:13:23.302772+00:00
-- url     : https://prove2.me/submissions/7e428403-eab7-49f5-b1f7-b8a71f8876ae

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P45

open Filter

theorem solution (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    max (Real.log x) (Real.log y) ≤ Real.log (x+y) ∧
    Real.log (x+y) ≤ max (Real.log x) (Real.log y)+Real.log 2 := by
  constructor
  · exact max_le (Real.log_le_log hx (by linarith)) (Real.log_le_log hy (by linarith))
  · rcases le_total x y with h | h
    · have h2 : x + y ≤ 2 * y := by linarith
      have h3 := Real.log_le_log (by linarith) h2
      rw [Real.log_mul (by norm_num) hy.ne'] at h3
      have h4 := le_max_right (Real.log x) (Real.log y)
      linarith
    · have h2 : x + y ≤ 2 * x := by linarith
      have h3 := Real.log_le_log (by linarith) h2
      rw [Real.log_mul (by norm_num) hx.ne'] at h3
      have h4 := le_max_left (Real.log x) (Real.log y)
      linarith
