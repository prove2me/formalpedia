-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_thirtyone_residual_order_absurd_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-16T16:53:11.782312+00:00
-- url     : https://prove2.me/submissions/907bf84f-8bff-4f6d-b03d-b908abdce311

import Mathlib

theorem solution (D q4 : Nat)
    (hcase :
      (D = 15 ∧
        ((q4 = 61 ∧ orderOf (3 : ZMod q4) = 10) ∨
          (q4 = 151 ∧ orderOf (3 : ZMod q4) = 50))) ∨
      (D = 27 ∧ q4 = 61 ∧ orderOf (3 : ZMod q4) = 10) ∨
      (D = 31 ∧ q4 = 61 ∧ orderOf (3 : ZMod q4) = 10) ∨
      (D = 45 ∧ q4 = 41 ∧ orderOf (3 : ZMod q4) = 8) ∨
      (D = 75 ∧ q4 = 37 ∧ orderOf (3 : ZMod q4) = 18))
    (hindex : Nat.Prime (orderOf (3 : ZMod q4))) : False := by
  rcases hcase with h15 | h27 | h31 | h45 | h75
  · rcases h15 with ⟨_, h⟩
    rcases h with h | h
    · rcases h with ⟨_, ho⟩
      rw [ho] at hindex
      norm_num at hindex
    · rcases h with ⟨_, ho⟩
      rw [ho] at hindex
      norm_num at hindex
  · rcases h27 with ⟨_, _, ho⟩
    rw [ho] at hindex
    norm_num at hindex
  · rcases h31 with ⟨_, _, ho⟩
    rw [ho] at hindex
    norm_num at hindex
  · rcases h45 with ⟨_, _, ho⟩
    rw [ho] at hindex
    norm_num at hindex
  · rcases h75 with ⟨_, _, ho⟩
    rw [ho] at hindex
    norm_num at hindex
