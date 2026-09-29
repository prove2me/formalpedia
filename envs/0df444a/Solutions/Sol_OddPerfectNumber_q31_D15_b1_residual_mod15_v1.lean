-- Prove2me | solution 1 for OddPerfectNumber.q31_D15_b1_residual_mod15_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T17:05:47.472867+00:00
-- url     : https://prove2.me/submissions/3a850f44-e4ea-4904-bd33-28c6ae5a7560

import Mathlib

theorem solution (q4 : Nat)
    (hprime : q4.Prime) (hlo : 31 < q4)
    (h3 : 3 ∣ orderOf (3 : ZMod q4)) (h5 : 5 ∣ orderOf (3 : ZMod q4)) :
    q4 % 15 = 1 := by
  haveI : NeZero q4 := ⟨by omega⟩
  haveI : Fact q4.Prime := ⟨hprime⟩
  have h15 : 15 ∣ orderOf (3 : ZMod q4) := by
    have h35 : Nat.Coprime 3 5 := by norm_num
    have := h35.mul_dvd_of_dvd_of_dvd h3 h5
    norm_num at this
    norm_num
    exact this
  have hne : (3 : ZMod q4) ≠ 0 := by
    intro h
    have h3c : ((3 : ℕ) : ZMod q4) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h3c
    have hle : q4 ≤ 3 := Nat.le_of_dvd (by norm_num) h3c
    clear h3 h5 h15 h
    omega
  have hferm : (3 : ZMod q4) ^ (q4 - 1) = 1 := ZMod.pow_card_sub_one_eq_one hne
  have hdvd : orderOf (3 : ZMod q4) ∣ q4 - 1 := orderOf_dvd_of_pow_eq_one hferm
  have h15dvd : 15 ∣ q4 - 1 := dvd_trans h15 hdvd
  obtain ⟨k, hk⟩ := h15dvd
  have hq2 : q4 = 1 + k * 15 := by
    have g1 : 1 ≤ q4 := by omega
    calc q4 = q4 - 1 + 1 := (Nat.sub_add_cancel g1).symm
      _ = 15 * k + 1 := by rw [hk]
      _ = 1 + k * 15 := by ring
  rw [hq2, mul_comm k 15, Nat.add_mul_mod_self_left]
