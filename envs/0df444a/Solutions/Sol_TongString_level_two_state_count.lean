-- Prove2me | solution 1 for TongString.level_two_state_count
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T14:31:46.502124+00:00
-- url     : https://prove2.me/submissions/87593695-7f5d-4f23-abfd-4f0f02c0ba85

import Mathlib

theorem solution (D : ℕ) (hD : 2 ≤ D) :
    Fintype.card (Sym2 (Fin (D - 2))) + (D - 2) = D * (D - 1) / 2 - 1 := by
  obtain ⟨n, rfl⟩ : ∃ n, D = n + 2 := ⟨D - 2, by omega⟩
  rw [Sym2.card, Fintype.card_fin]
  simp only [Nat.add_sub_cancel]
  rw [Nat.choose_two_right]
  have h1 : (n + 2) * (n + 2 - 1) = (n + 2) * (n + 1) := by
    congr 1
  rw [h1]
  have e1 : (n + 1) * (n + 1 - 1) = n * (n + 1) := by
    rw [Nat.add_sub_cancel, mul_comm]
  rw [e1]
  have ev1 : 2 ∣ n * (n + 1) := (Nat.even_mul_succ_self n).two_dvd
  have ev2 : (n + 2) * (n + 1) = n * (n + 1) + 2 * (n + 1) := by ring
  rw [ev2]
  omega
