-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_extension__p2m_fe1c41f8_8086_4f84_bd8f_45d16a4fd3f9_a1
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T16:43:45.047803+00:00
-- url     : https://prove2.me/submissions/cdc0e906-1ac4-42f7-8206-c45e159da1a0

import Mathlib

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (P : SimpleGraph V → Prop) (hP : P G) :
    ∃ H : SimpleGraph V, G ≤ H ∧ P H ∧ ∀ Y : SimpleGraph V, H ≤ Y → P Y → Y ≤ H := by
  let p : SimpleGraph V → Prop := fun H => G ≤ H ∧ P H
  have hpG : p G := ⟨le_rfl, hP⟩
  obtain ⟨H, hGH, hHmax⟩ :=
    (Finite.exists_le_maximal (α := SimpleGraph V) (p := p) (a := G) hpG)
  rcases hHmax with ⟨hHp, hHmax'⟩
  refine ⟨H, hHp.1, hHp.2, ?_⟩
  intro Y hHY hPY
  exact hHmax' ⟨hHp.1.trans hHY, hPY⟩ hHY
