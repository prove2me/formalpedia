-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentythree_D27_sigma_div_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-15T08:01:54.238898+00:00
-- url     : https://prove2.me/submissions/4cd0e765-8ed8-4ed5-a353-2ac5d8b862f5

import Mathlib

theorem solution (m D p sigma : Nat)
    (hrel : D * sigma = p * m ^ 2)
    (hD : D = 27)
    (hp_eq : p = 2 * D - 1) :
    53 ∣ sigma := by
  subst D
  norm_num at hp_eq
  have hrel' : 27 * sigma = 53 * m ^ 2 := by
    simpa [hp_eq] using hrel
  have hdvd : 53 ∣ 27 * sigma := by
    refine ⟨m ^ 2, ?_⟩
    exact hrel'
  exact (by norm_num : Nat.Coprime 53 27).dvd_of_dvd_mul_left hdvd
