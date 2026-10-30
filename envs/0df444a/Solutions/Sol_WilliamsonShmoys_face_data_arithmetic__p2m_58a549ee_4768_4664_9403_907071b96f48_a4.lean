-- Prove2me | solution 1 for WilliamsonShmoys.face_data_arithmetic__p2m_58a549ee_4768_4664_9403_907071b96f48_a4
-- status  : ACCEPTED   (disprove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-29T06:40:44.90799+00:00
-- url     : https://prove2.me/submissions/de052442-e4ff-4ced-bc39-e7bab7a22b05

import Mathlib
open scoped BigOperators

theorem solution : ¬ (∀ (n m : Nat) (hn : 3 ≤ n) (hlow : n ≤ m + 2) (hupp : m ≤ 3 * n - 6),
    ∃ (F : Type) (inst : Fintype F) (length : F → Nat),
      n + @Fintype.card F inst = m + 2 ∧ (∀ f : F, 3 ≤ length f) ∧
      (letI : Fintype F := inst; (∑ f : F, length f) = 2 * m)) := by
  intro h
  obtain ⟨F, inst, length, hc, _, hs⟩ := h 3 1 (by norm_num) (by norm_num) (by norm_num)
  have hcard : @Fintype.card F inst = 0 := by omega
  have hempty : IsEmpty F := by
    have := @Fintype.card_eq_zero_iff F inst
    exact this.1 hcard
  have : (∑ f : F, length f) = 0 := by
    letI : Fintype F := inst
    exact Finset.sum_eq_zero (fun f _ => (hempty.false f).elim)
  letI : Fintype F := inst
  omega
