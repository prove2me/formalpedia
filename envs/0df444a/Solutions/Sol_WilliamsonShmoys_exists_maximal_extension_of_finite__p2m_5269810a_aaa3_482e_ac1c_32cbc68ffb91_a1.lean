-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_extension_of_finite__p2m_5269810a_aaa3_482e_ac1c_32cbc68ffb91_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:51:48.556329+00:00
-- url     : https://prove2.me/submissions/69cfd05b-31ba-411b-b93a-53b972a1f111

import Mathlib

open SimpleGraph

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop)
    (hhered : ∀ {G H : SimpleGraph V}, G ≤ H → P H → P G)
    (G : SimpleGraph V) (hG : P G) :
    ∃ K : SimpleGraph V, G ≤ K ∧ P K ∧
      ∀ L : SimpleGraph V, K ≤ L → P L → L ≤ K := by
  classical
  let s : Set (SimpleGraph V) := {K | G ≤ K ∧ P K}
  have hs : s.Nonempty := ⟨G, le_rfl, hG⟩
  obtain ⟨K, hK, hmax⟩ := s.toFinite.exists_maximal hs
  refine ⟨K, hK.1, hK.2, ?_⟩
  intro L hKL hPL
  have hL : L ∈ s := ⟨hK.1.trans hKL, hPL⟩
  exact hmax hL hKL