-- Prove2me | solution 1 for WilliamsonShmoys.face_data_arithmetic_connected__p2m_58a549ee_4768_4664_9403_907071b96f48_a5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T07:48:19.315653+00:00
-- url     : https://prove2.me/submissions/6007840e-2a2d-4843-9e96-dd98842fb8b7

import Mathlib

theorem solution (n m : Nat) (hn : 3 ≤ n) (hlow : n ≤ m + 1) (hupp : m ≤ 3 * n - 6) : ∃ (F : Type) (inst : Fintype F) (length : F → Nat), n + @Fintype.card F inst = m + 2 ∧ (∀ f : F, 3 ≤ length f) ∧ (letI : Fintype F := inst; (∑ f : F, length f) = 2 * m) := by
  obtain ⟨k, hk⟩ : ∃ k, m + 2 - n = k + 1 := ⟨m + 1 - n, by omega⟩
  refine ⟨Fin (k + 1), inferInstance, fun i => if i = 0 then 2 * m - 3 * k else 3, ?_, ?_, ?_⟩
  · simp; omega
  · intro i; dsimp only; split_ifs <;> omega
  · rw [Fin.sum_univ_succ]
    simp only [Fin.succ_ne_zero, if_false, if_true, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul]
    omega
