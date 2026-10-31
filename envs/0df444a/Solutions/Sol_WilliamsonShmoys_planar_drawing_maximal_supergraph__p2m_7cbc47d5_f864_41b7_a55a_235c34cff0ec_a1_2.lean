-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_7cbc47d5_f864_41b7_a55a_235c34cff0ec_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:27:49.797025+00:00
-- url     : https://prove2.me/submissions/f2a0bd52-3e0a-4ccc-93aa-677f688e20e9

import Theorems.Thm_WilliamsonShmoys_planar_maximal_completion__p2m_faad2303_0a65_471d_a30c_3c1398903a00_a1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ HasPlanarDrawingOn H ∧
      G.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      (∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K ≤ H) :=
  WilliamsonShmoys.planar_maximal_completion__p2m_faad2303_0a65_471d_a30c_3c1398903a00_a1 G hG
