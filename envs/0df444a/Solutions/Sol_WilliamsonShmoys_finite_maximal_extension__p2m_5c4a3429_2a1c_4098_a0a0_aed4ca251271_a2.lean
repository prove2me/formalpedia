-- Prove2me | solution 1 for WilliamsonShmoys.finite_maximal_extension__p2m_5c4a3429_2a1c_4098_a0a0_aed4ca251271_a2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:59:22.33352+00:00
-- url     : https://prove2.me/submissions/5c982f5a-3e8c-4e2c-ada8-e0c693c1dff0

import Mathlib

namespace S216WS

lemma exists_maximal {V : Type} [Fintype V] (W : SimpleGraph V) (P : SimpleGraph V → Prop)
    (hP : P W) : ∃ H : SimpleGraph V, W ≤ H ∧ P H ∧
      ∀ K : SimpleGraph V, H ≤ K → P K → K = H := by
  obtain ⟨H, ⟨hWH, hPH⟩, hmax⟩ := Set.Finite.exists_maximal
    (s := {G : SimpleGraph V | W ≤ G ∧ P G}) (Set.toFinite _) ⟨W, le_rfl, hP⟩
  exact ⟨H, hWH, hPH, fun K hHK hPK => le_antisymm (hmax ⟨le_trans hWH hHK, hPK⟩ hHK) hHK⟩

end S216WS


theorem solution
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop)
    (hmono : ∀ {G H : SimpleGraph V}, G ≤ H → P H → P G)
    (R : SimpleGraph V)
    (hR : P R) :
    ∃ H : SimpleGraph V,
      R ≤ H ∧ P H ∧
      ∀ K : SimpleGraph V, H ≤ K → P K → K = H := S216WS.exists_maximal R P hR
