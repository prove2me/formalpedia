-- Prove2me | solution 1 for WilliamsonShmoys.exists_edgeMaximalPlanarSupergraph__p2m_dcc74752_2897_43b5_8a61_1f7227b8dfbf_a3__p2m_dcc74752_2897_43b5_8a61_1f7227b8dfbf_a4
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:50:55.726742+00:00
-- url     : https://prove2.me/submissions/3134b919-9486-40c5-96a4-79b2666019a0

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn G) :
    ∃ N : SimpleGraph V, G ≤ N ∧ HasPlanarDrawingOn N ∧
      (∀ M : SimpleGraph V, N ≤ M → HasPlanarDrawingOn M → M = N) := by
  let S : Set (SimpleGraph V) := {N | G ≤ N ∧ HasPlanarDrawingOn N}
  have hS : S.Finite := Set.toFinite S
  obtain ⟨N, hN⟩ := hS.exists_maximal ⟨G, le_rfl, hDraw⟩
  refine ⟨N, hN.1.1, hN.1.2, ?_⟩
  intro M hNM hM
  have hMmem : M ∈ S := ⟨hN.1.1.trans hNM, hM⟩
  have hMN : M ≤ N := hN.2 hMmem hNM
  exact le_antisymm hMN hNM