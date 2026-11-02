-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_6d91b10d_a30f_4f1a_8acb_96a7ed12e6b9_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T13:08:36.894931+00:00
-- url     : https://prove2.me/submissions/088ef00b-7309-4a12-b21c-79c18af99436
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_euler_certificate__p2m_844ee2d0_ef82_4c36_8373_ea0ee656ba91_a2
import Theorems.Thm_WilliamsonShmoys_euler_face_data_implies_edge_bound__p2m_844ee2d0_ef82_4c36_8373_ea0ee656ba91_a2

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hGdraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel G.Adj := Classical.decRel G.Adj
     G.edgeFinset.card) + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, f, hGH, hedge, heuler, hfaces⟩ :=
    WilliamsonShmoys.planar_drawing_connected_euler_certificate__p2m_844ee2d0_ef82_4c36_8373_ea0ee656ba91_a2
      G hGdraw hcard
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  exact WilliamsonShmoys.euler_face_data_implies_edge_bound__p2m_844ee2d0_ef82_4c36_8373_ea0ee656ba91_a2
    (Fintype.card V) G.edgeFinset.card H.edgeFinset.card f hcard hedge heuler hfaces