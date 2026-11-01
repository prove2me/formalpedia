-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_edge_bound__p2m_a2d35d35_9ed8_4ba3_917d_fe0f629ebdbd_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:22:32.259168+00:00
-- url     : https://prove2.me/submissions/21141308-10cc-477b-abd9-c66608615d73

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_25a042c7_1a1b_47c9_a392_cae86f15b395_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_25a042c7_1a1b_47c9_a392_cae86f15b395_a2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hcard : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      H.edgeSet.ncard ≤ K.edgeSet.ncard ∧
      K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨K, hHK, hKdraw, hmax, hedge⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_25a042c7_1a1b_47c9_a392_cae86f15b395_a2
      H hcard hH
  exact ⟨K, hHK, hKdraw, hedge,
    WilliamsonShmoys.maximal_planar_edge_count__p2m_25a042c7_1a1b_47c9_a392_cae86f15b395_a2
      K hcard hKdraw hmax⟩