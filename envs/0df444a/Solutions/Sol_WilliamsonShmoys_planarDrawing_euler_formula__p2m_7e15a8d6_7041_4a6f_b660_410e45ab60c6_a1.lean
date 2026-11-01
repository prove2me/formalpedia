-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawing_euler_formula__p2m_7e15a8d6_7041_4a6f_b660_410e45ab60c6_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-01T05:19:49.317658+00:00
-- url     : https://prove2.me/submissions/10518fe8-c5e8-4fdc-827e-2055ccfb17b8

import Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_formula__p2m_89410822_d74b_4a7e_a2

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hconn : G.Connected)
    (hG : HasPlanarDrawingOn G) :
    ∃ f : ℕ,
      Fintype.card V + f = (letI : DecidableRel G.Adj := dG; G.edgeFinset.card) + 2 :=
  WilliamsonShmoys.planar_drawing_euler_formula__p2m_89410822_d74b_4a7e_a2 G dG hG hconn
