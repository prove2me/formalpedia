-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_extension__p2m_2e520467_0d96_4c71_b340_b60069871ecd_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:50:59.510089+00:00
-- url     : https://prove2.me/submissions/b2be9485-efc7-4f75-901e-823a5aa77876
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension_core__p2m_a22916a4_7a8b_4f53_bd03_4020e8e3faca_a2
open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, H ≤ K ∧ H.edgeSet.ncard ≤ K.edgeSet.ncard ∧
      K.Connected ∧ HasPlanarDrawingOn K := by
  obtain ⟨K, hHK, hconn, hplanar⟩ :=
    WilliamsonShmoys.planar_drawing_connected_extension_core__p2m_a22916a4_7a8b_4f53_bd03_4020e8e3faca_a2 H hH
  refine ⟨K, hHK, ?_, hconn, hplanar⟩
  exact Set.ncard_mono (SimpleGraph.edgeSet_mono hHK)