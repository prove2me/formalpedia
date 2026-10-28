-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximum_nat_rank
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T02:39:30.367835+00:00
-- url     : https://prove2.me/submissions/8584d1a0-086c-45dc-86d1-59e9d32d82f3

import Mathlib
set_option autoImplicit false

theorem solution
    {α : Type} (S : α → Prop) (r : α → Nat) (N : Nat)
    (hne : ∃ a, S a)
    (hbound : ∀ a, S a → r a ≤ N) :
    ∃ a, S a ∧ ∀ b, S b → r b ≤ r a := by
  classical
  obtain ⟨a0, ha0⟩ := hne
  let p : ℕ → Prop := fun n => ∃ a, S a ∧ r a = n
  have hspec : p (Nat.findGreatest p N) :=
    Nat.findGreatest_spec (P := p) (hbound a0 ha0) ⟨a0, ha0, rfl⟩
  obtain ⟨a, ha, hra⟩ := hspec
  refine ⟨a, ha, fun b hb => ?_⟩
  rw [hra]
  exact Nat.le_findGreatest (hbound b hb) ⟨b, hb, rfl⟩
