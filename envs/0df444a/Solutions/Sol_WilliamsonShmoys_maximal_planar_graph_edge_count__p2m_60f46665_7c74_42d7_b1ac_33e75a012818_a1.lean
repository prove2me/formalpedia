-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_60f46665_7c74_42d7_b1ac_33e75a012818_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:28:47.243273+00:00
-- url     : https://prove2.me/submissions/0b66f3d7-ad2d-4d0f-bfab-ce4418f85572

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension_edge_count__p2m_92179202_75fd_4ebd_82a2_e854a66d92bd_a2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ M : SimpleGraph V, L.edgeSet ⊆ M.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn M → M.edgeSet = L.edgeSet) :
    L.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨T, hsub, hTplanar, hTcount⟩ :=
    WilliamsonShmoys.planar_triangulation_extension_edge_count__p2m_92179202_75fd_4ebd_82a2_e854a66d92bd_a2
      L hL hcard
  have hEq : T.edgeSet = L.edgeSet := hmax T hsub hTplanar
  simpa [hEq] using hTcount