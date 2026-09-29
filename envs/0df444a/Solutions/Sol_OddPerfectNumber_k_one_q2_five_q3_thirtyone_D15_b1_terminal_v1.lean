-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_thirtyone_D15_b1_terminal_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T16:52:40.652178+00:00
-- url     : https://prove2.me/submissions/b689ff9c-9aa4-4411-ad8a-c05fd30c488f

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirtyone_residual_order_absurd_v1

theorem solution (D q4 : Nat)
    (hD : D = 15) (hq : q4 = 61 ∨ q4 = 151)
    (ho61 : q4 = 61 → orderOf (3 : ZMod q4) = 10)
    (ho151 : q4 = 151 → orderOf (3 : ZMod q4) = 50)
    (hindex : Nat.Prime (orderOf (3 : ZMod q4))) : False := by
  have hcase : (D = 15 ∧ ((q4 = 61 ∧ orderOf (3 : ZMod q4) = 10) ∨ (q4 = 151 ∧ orderOf (3 : ZMod q4) = 50))) ∨ (D = 27 ∧ q4 = 61 ∧ orderOf (3 : ZMod q4) = 10) ∨ (D = 31 ∧ q4 = 61 ∧ orderOf (3 : ZMod q4) = 10) ∨ (D = 45 ∧ q4 = 41 ∧ orderOf (3 : ZMod q4) = 8) ∨ (D = 75 ∧ q4 = 37 ∧ orderOf (3 : ZMod q4) = 18) := by
    rcases hq with h61 | h151
    · exact Or.inl ⟨hD, Or.inl ⟨h61, ho61 h61⟩⟩
    · exact Or.inl ⟨hD, Or.inr ⟨h151, ho151 h151⟩⟩
  exact OddPerfectNumber.k_one_q2_five_q3_thirtyone_residual_order_absurd_v1 D q4 hcase hindex
