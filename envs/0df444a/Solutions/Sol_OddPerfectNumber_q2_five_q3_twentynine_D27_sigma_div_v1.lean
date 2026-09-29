-- Prove2me | solution 1 for OddPerfectNumber.q2_five_q3_twentynine_D27_sigma_div_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-16T14:05:47.076258+00:00
-- url     : https://prove2.me/submissions/3e92a03e-5bf9-4d98-81e1-4059259a0f25

import Mathlib

theorem solution (D p sigma m : Nat)
    (hrel : D * sigma = p * m ^ 2)
    (hD : D = 27) (hp_eq : p = 2 * D - 1) :
    53 ∣ sigma := by
  have hrel' := hrel
  have hp53 : p = 53 := by omega
  rw [hD, hp53] at hrel'
  have hdiv : 53 ∣ 27 * sigma := by
    refine ⟨m ^ 2, ?_⟩
    exact hrel'
  rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 53)).mp hdiv with h27 | hsigma
  · norm_num at h27
  · exact hsigma
