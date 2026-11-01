-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_simple_graph_edge_lower_bound__p2m_04b260ca_6bc4_40b7_9582_99be510cc2b0_a3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:17:47.434879+00:00
-- url     : https://prove2.me/submissions/cd6d7ae6-4374-4655-891e-65c117f87b7e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_edge_saturated_planar_graph_edge_lower_bound__p2m_af9692fd_71ca_4e9b_bb88_c2808556729a_a3
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V,
      H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H) :
    3 * Fintype.card V ≤ H.edgeSet.ncard + 6 := by
  apply WilliamsonShmoys.edge_saturated_planar_graph_edge_lower_bound__p2m_af9692fd_71ca_4e9b_bb88_c2808556729a_a3 H hcard hH
  intro u v huv hnot K hle hadj hK
  have hKH : K ≤ H := hmax K hle hK
  exact hnot (hKH hadj)