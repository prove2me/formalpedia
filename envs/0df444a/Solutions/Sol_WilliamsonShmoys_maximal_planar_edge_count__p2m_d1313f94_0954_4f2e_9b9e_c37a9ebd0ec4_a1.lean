-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_d1313f94_0954_4f2e_9b9e_c37a9ebd0ec4_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T20:24:09.933663+00:00
-- url     : https://prove2.me/submissions/3342fc72-810b-4602-9e67-4b95a30b9cbb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_completion_exact_edge_count__p2m_e9f7baec_2042_4774_99e6_a1421ec04a69_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ N : SimpleGraph V,
      Set.Subset M.edgeSet N.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn N →
      Set.Subset N.edgeSet M.edgeSet) :
    3 * Fintype.card V = M.edgeSet.ncard + 6 := by
  obtain ⟨N, hMN, hN, hCount⟩ :=
    WilliamsonShmoys.exists_planar_completion_exact_edge_count__p2m_e9f7baec_2042_4774_99e6_a1421ec04a69_a1
      M hM hCard
  have hNM : Set.Subset N.edgeSet M.edgeSet := hMax N hMN hN
  have hEdges : M.edgeSet = N.edgeSet := Set.Subset.antisymm hMN hNM
  rw [hEdges, hCount]