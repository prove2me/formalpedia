-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_completion_maximal__p2m_dbc1909c_e0b1_4b52_8a1f_f063e3dc8217_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:46:40.833214+00:00
-- url     : https://prove2.me/submissions/1835857c-c16f-4485-aad6-06e90e5a5d50

import Theorems.Thm_WilliamsonShmoys_maximal_planar_extension

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hDraw : HasPlanarDrawingOn G) : ∃ H : SimpleGraph V, G.edgeSet ⊆ H.edgeSet ∧ HasPlanarDrawingOn H ∧ (∀ K : SimpleGraph V, H.edgeSet ⊆ K.edgeSet → HasPlanarDrawingOn K → K = H) :=
  WilliamsonShmoys.maximal_planar_extension G hDraw
