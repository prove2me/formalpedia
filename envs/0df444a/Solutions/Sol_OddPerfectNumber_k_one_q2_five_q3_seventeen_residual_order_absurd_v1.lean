-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_seventeen_residual_order_absurd_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-16T16:51:57.772991+00:00
-- url     : https://prove2.me/submissions/c1f93f51-4881-4340-afdf-9a765fec6772

import Mathlib

theorem solution (D q4 : Nat) (hq4 : q4.Prime)
    (hcase :
      (D = 135 ∧
        ((q4 = 1021 ∧ orderOf (3 : ZMod q4) = 34) ∨
          (q4 = 1531 ∧ orderOf (3 : ZMod q4) = 170) ∨
          (q4 = 2551 ∧ orderOf (3 : ZMod q4) = 150) ∨
          (q4 = 3061 ∧ orderOf (3 : ZMod q4) = 1530) ∨
          (q4 = 3571 ∧ orderOf (3 : ZMod q4) = 3570) ∨
          (q4 = 4591 ∧ orderOf (3 : ZMod q4) = 270))) ∨
      (D = 225 ∧
        ((q4 = 103 ∧ orderOf (3 : ZMod q4) = 34) ∨
          (q4 = 137 ∧ orderOf (3 : ZMod q4) = 136) ∨
          (q4 = 239 ∧ orderOf (3 : ZMod q4) = 119) ∨
          (q4 = 307 ∧ orderOf (3 : ZMod q4) = 34) ∨
          (q4 = 409 ∧ orderOf (3 : ZMod q4) = 204) ∨
          (q4 = 443 ∧ orderOf (3 : ZMod q4) = 221))) ∨
      (D = 255 ∧ q4 = 511) ∨
      (D = 289 ∧
        ((q4 = 31 ∧ orderOf (3 : ZMod q4) = 30) ∨
          (q4 = 61 ∧ orderOf (3 : ZMod q4) = 10) ∨
          (q4 = 151 ∧ orderOf (3 : ZMod q4) = 50) ∨
          (q4 = 181 ∧ orderOf (3 : ZMod q4) = 45) ∨
          (q4 = 211 ∧ orderOf (3 : ZMod q4) = 210) ∨
          (q4 = 241 ∧ orderOf (3 : ZMod q4) = 120) ∨
          (q4 = 271 ∧ orderOf (3 : ZMod q4) = 30) ∨
          (q4 = 331 ∧ orderOf (3 : ZMod q4) = 330) ∨
          (q4 = 421 ∧ orderOf (3 : ZMod q4) = 105))))
    (hindex : Nat.Prime (orderOf (3 : ZMod q4))) : False := by
  rcases hcase with h135 | h225 | h255 | h289
  · rcases h135 with ⟨_, h⟩
    rcases h with h | h | h | h | h | h
    all_goals rcases h with ⟨_, ho⟩
    all_goals rw [ho] at hindex
    all_goals norm_num at hindex
  · rcases h225 with ⟨_, h⟩
    rcases h with h | h | h | h | h | h
    all_goals rcases h with ⟨_, ho⟩
    all_goals rw [ho] at hindex
    all_goals norm_num at hindex
  · rcases h255 with ⟨_, hq⟩
    have : q4 = 511 := hq
    rw [this] at hq4
    norm_num at hq4
  · rcases h289 with ⟨_, h⟩
    rcases h with h | h | h | h | h | h | h | h | h
    all_goals rcases h with ⟨_, ho⟩
    all_goals rw [ho] at hindex
    all_goals norm_num at hindex
