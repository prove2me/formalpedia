-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_property_extension__p2m_a49e8573_7163_46f3_bc6a_b6dc614057e1_a1
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T16:44:19.395795+00:00
-- url     : https://prove2.me/submissions/1b804a5f-5510-4fe3-8985-e0823a58cef3

import Mathlib

theorem solution
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop)
    (K : SimpleGraph V)
    (hK : P K) :
    ∃ M : SimpleGraph V, K ≤ M ∧ P M ∧ ∀ G : SimpleGraph V, M ≤ G → P G → G = M := by
  classical
  let p : SimpleGraph V → Prop := fun X => K ≤ X ∧ P X
  have hpK : p K := ⟨le_rfl, hK⟩
  obtain ⟨M, hKM, hMmax⟩ :=
    (Finite.exists_le_maximal (α := SimpleGraph V) (p := p) (a := K) hpK)
  rcases hMmax with ⟨hMp, hMmax'⟩
  refine ⟨M, hKM, hMp.2, ?_⟩
  intro G hMG hPG
  have hpG : p G := ⟨hKM.trans hMG, hPG⟩
  exact (le_antisymm hMG (hMmax' hpG hMG)).symm
