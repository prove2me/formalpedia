-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_supergraph__p2m_ff0df929_a528_472b_801c_6c58169000bb_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-01T05:16:30.372273+00:00
-- url     : https://prove2.me/submissions/2be9c900-33ea-4054-8f16-fc52c37bc3ec

import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_completion__p2m_a893531d_2eaf_40a4_93f3_f4bc4ca725ea_a3

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hplanar : HasPlanarDrawingOn G)
    (hconn : G.Connected)
    (hcard : 3 <= Fintype.card V) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧
      HasPlanarDrawingOn H ∧
      G.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V :=
  WilliamsonShmoys.planar_drawing_triangulation_completion__p2m_a893531d_2eaf_40a4_93f3_f4bc4ca725ea_a3 G hplanar hcard
