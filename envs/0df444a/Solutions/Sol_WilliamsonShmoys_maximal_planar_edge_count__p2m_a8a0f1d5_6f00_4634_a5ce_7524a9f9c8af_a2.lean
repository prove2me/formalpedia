-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_a8a0f1d5_6f00_4634_a5ce_7524a9f9c8af_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T19:47:16.476163+00:00
-- url     : https://prove2.me/submissions/43c7d080-541a-4edf-b2cb-2dc2a1c5469e

import Theorems.Thm_WilliamsonShmoys_maximal_planar_triangulation_extension__p2m_b4f3c7d0_f80f_4201_8b80_29190a270a03_a1

set_option autoImplicit false

 theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V,
      Set.Subset L.edgeSet M.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn M →
      Set.Subset M.edgeSet L.edgeSet)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V = L.edgeSet.ncard + 6 := by
  obtain ⟨M, hLM, hM, hCount⟩ :=
    WilliamsonShmoys.maximal_planar_triangulation_extension__p2m_b4f3c7d0_f80f_4201_8b80_29190a270a03_a1
      L hL hCard
  have hML : Set.Subset M.edgeSet L.edgeSet := hMax M hLM hM
  have hEq : L.edgeSet = M.edgeSet := Set.Subset.antisymm hLM hML
  rw [← hEq] at hCount
  exact hCount