-- Prove2me | solution 1 for WilliamsonShmoys.exists_bounded_score_max__p2m_bf9a75f5_fb19_4298_9037_82dd49bb2208_a1
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T16:17:37.581276+00:00
-- url     : https://prove2.me/submissions/0bcd6749-634e-4004-bd74-2075e868f349

import Mathlib

theorem solution {α : Type} (s : α → Prop) (score : α → Nat) (B : Nat)
    (hbound : ∀ a, s a → score a ≤ B) (hne : ∃ a, s a) :
    ∃ a, s a ∧ ∀ b, s b → score b ≤ score a := by
  classical
  let P : Nat → Prop := fun k => ∃ a, s a ∧ score a = k
  rcases hne with ⟨a0, ha0⟩
  have hPa0 : P (score a0) := ⟨a0, ha0, rfl⟩
  have hle0 : score a0 ≤ B := hbound a0 ha0
  let k := Nat.findGreatest P B
  have hPk : P k := by
    dsimp [k]
    exact Nat.findGreatest_spec hle0 hPa0
  rcases hPk with ⟨a, ha, hka⟩
  refine ⟨a, ha, ?_⟩
  intro b hb
  have hbB : score b ≤ B := hbound b hb
  have hPb : P (score b) := ⟨b, hb, rfl⟩
  have hle : score b ≤ k := by
    dsimp [k]
    exact Nat.le_findGreatest hbB hPb
  omega
