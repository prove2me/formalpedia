-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_04b260ca_6bc4_40b7_9582_99be510cc2b0_a3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:12:35.918128+00:00
-- url     : https://prove2.me/submissions/d99cdb38-9316-4a89-b8c0-4c5e01c990ad
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation__p2m_b2bd6a42_fcd9_4968_a08e_3c940e955daf_a1
import Theorems.Thm_WilliamsonShmoys_edgeSet_ncard_mono__p2m_b2bd6a42_fcd9_4968_a08e_3c940e955daf_a1
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hsub, hbound⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation__p2m_b2bd6a42_fcd9_4968_a08e_3c940e955daf_a1
      G hcard hG
  have hmono :=
    WilliamsonShmoys.edgeSet_ncard_mono__p2m_b2bd6a42_fcd9_4968_a08e_3c940e955daf_a1
      G H hsub
  omega