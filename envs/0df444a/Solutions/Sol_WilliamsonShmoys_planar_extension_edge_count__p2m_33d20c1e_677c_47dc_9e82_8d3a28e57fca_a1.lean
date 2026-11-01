-- Prove2me | solution 1 for WilliamsonShmoys.planar_extension_edge_count__p2m_33d20c1e_677c_47dc_9e82_8d3a28e57fca_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:07:23.591646+00:00
-- url     : https://prove2.me/submissions/003a35eb-d6f2-422a-8d82-04797e00db84
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_extension_exists__p2m_8c081704_c431_4561_a79b_9bf3229669d7_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_exact_edge_count__p2m_8c081704_c431_4561_a79b_9bf3229669d7_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V,
      M.edgeSet ⊆ N.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      N.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨N, hMN, hN, hmax⟩ :=
    WilliamsonShmoys.maximal_planar_extension_exists__p2m_8c081704_c431_4561_a79b_9bf3229669d7_a1
      M hM
  have hcount :=
    WilliamsonShmoys.maximal_planar_graph_exact_edge_count__p2m_8c081704_c431_4561_a79b_9bf3229669d7_a1
      N hN hcard hmax
  exact ⟨N, hMN, hN, hcount⟩