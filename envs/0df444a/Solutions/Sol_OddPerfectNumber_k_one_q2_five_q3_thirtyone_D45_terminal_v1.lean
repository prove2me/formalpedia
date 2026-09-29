-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_thirtyone_D45_terminal_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T16:58:03.463415+00:00
-- url     : https://prove2.me/submissions/31d8fbcb-938f-4cfd-88d4-a4affc9be20f

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirtyone_residual_order_absurd_v1

theorem solution (D q4 : Nat)
    (hD : D = 45) (hq : q4 = 41) (ho : orderOf (3 : ZMod q4) = 8)
    (hindex : Nat.Prime (orderOf (3 : ZMod q4))) : False := by
  have hcase : (D = 15 ∧ ((q4 = 61 ∧ orderOf (3 : ZMod q4) = 10) ∨ (q4 = 151 ∧ orderOf (3 : ZMod q4) = 50))) ∨ (D = 27 ∧ q4 = 61 ∧ orderOf (3 : ZMod q4) = 10) ∨ (D = 31 ∧ q4 = 61 ∧ orderOf (3 : ZMod q4) = 10) ∨ (D = 45 ∧ q4 = 41 ∧ orderOf (3 : ZMod q4) = 8) ∨ (D = 75 ∧ q4 = 37 ∧ orderOf (3 : ZMod q4) = 18) := Or.inr (Or.inr (Or.inr (Or.inl ⟨hD, hq, ho⟩)))
  exact OddPerfectNumber.k_one_q2_five_q3_thirtyone_residual_order_absurd_v1 D q4 hcase hindex
