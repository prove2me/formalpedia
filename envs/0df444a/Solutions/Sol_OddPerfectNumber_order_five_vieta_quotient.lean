-- Prove2me | solution 1 for OddPerfectNumber.order_five_vieta_quotient
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T18:41:37.722002+00:00
-- url     : https://prove2.me/submissions/b395eceb-13b3-40dc-b96e-83763ce735b1

import Mathlib
import Theorems.Thm_OddPerfectNumber_order_five_vieta_divisibility

open OddPerfectNumber

theorem solution (p q k : Nat)
    (hp : p.Prime)
    (hpk : p + 1 = q * k)
    (h5 : orderOf (q : ZMod p) = 5) :
    ∃ C : Nat, q ^ 2 + q + k ^ 2 + k + 1 = C * (q * k - 1) ∧ 0 < C := by
  have hdvd : p ∣ q ^ 2 + q + k ^ 2 + k + 1 :=
    order_five_vieta_divisibility p q k hp hpk h5
  obtain ⟨C, hC⟩ := hdvd
  have hpk1 : q * k - 1 = p := by omega
  have hCpos : 0 < C := by
    rcases Nat.eq_zero_or_pos C with h | h
    · rw [h, mul_zero] at hC
      omega
    · exact h
  refine ⟨C, ?_, hCpos⟩
  rw [hC, hpk1]
  exact mul_comm p C
