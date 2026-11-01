-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_extension_edge_count__p2m_92179202_75fd_4ebd_82a2_e854a66d92bd_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:36:11.815821+00:00
-- url     : https://prove2.me/submissions/0fef02b1-7ed1-48e8-ac19-f99fda7a37bb

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph__p2m_95f0e96c_588c_4293_a881_4eae330a335f_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_95f0e96c_588c_4293_a881_4eae330a335f_a1

set_option autoImplicit false

 theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ T : SimpleGraph V,
      L.edgeSet ⊆ T.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn T ∧
      T.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨T, hLT, hT, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_95f0e96c_588c_4293_a881_4eae330a335f_a1
      L hL
  refine ⟨T, hLT, hT, ?_⟩
  exact WilliamsonShmoys.maximal_planar_edge_count__p2m_95f0e96c_588c_4293_a881_4eae330a335f_a1
    T hT hmax hcard