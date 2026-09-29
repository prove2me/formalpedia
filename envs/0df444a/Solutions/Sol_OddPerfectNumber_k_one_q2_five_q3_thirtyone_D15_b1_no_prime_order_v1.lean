-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_thirtyone_D15_b1_no_prime_order_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T17:23:25.319068+00:00
-- url     : https://prove2.me/submissions/46d5f7df-224e-485e-825d-213704ad5bff

import Mathlib

theorem solution (q4 : Nat)
    (hq : q4 = 61 ∨ q4 = 151)
    (ho61 : q4 = 61 → orderOf (3 : ZMod q4) = 10)
    (ho151 : q4 = 151 → orderOf (3 : ZMod q4) = 50) :
    ¬ Nat.Prime (orderOf (3 : ZMod q4)) := by
  rcases hq with rfl | rfl
  · have ho := ho61 rfl
    rw [ho]
    norm_num
  · have ho := ho151 rfl
    rw [ho]
    norm_num
