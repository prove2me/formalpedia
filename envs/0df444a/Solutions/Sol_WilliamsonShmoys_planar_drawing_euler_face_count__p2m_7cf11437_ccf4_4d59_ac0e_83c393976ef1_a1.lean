-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_euler_face_count__p2m_7cf11437_ccf4_4d59_ac0e_83c393976ef1_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:03:10.883323+00:00
-- url     : https://prove2.me/submissions/bdfb3435-c218-4b98-8557-dfcc047308aa

import Theorems.Thm_WilliamsonShmoys_euler_from_crossing_free_arcs_eae47bd5

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (T : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hT : WilliamsonShmoys.HasPlanarDrawingOn T) (hconn : T.Connected) : ∃ f : ℕ, Fintype.card V + f = T.edgeSet.ncard + 2 :=
  WilliamsonShmoys.euler_from_crossing_free_arcs_eae47bd5 T hV hT hconn
