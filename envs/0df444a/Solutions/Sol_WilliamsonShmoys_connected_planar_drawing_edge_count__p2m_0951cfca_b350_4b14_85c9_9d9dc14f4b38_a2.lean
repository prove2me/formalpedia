-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_drawing_edge_count__p2m_0951cfca_b350_4b14_85c9_9d9dc14f4b38_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-03T03:51:33.194528+00:00
-- url     : https://prove2.me/submissions/7af4f7da-35b6-446a-8c92-29f425397bf7

import Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_edge_count__p2m_0951cfca_b350_4b14_85c9_9d9dc14f4b38_a3

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V) (hJ : WilliamsonShmoys.HasPlanarDrawingOn J)
    (hconn : ∀ u v : V, Nonempty (J.Walk u v))
    (hcard : 3 <= Fintype.card V) :
    letI : ∀ K : SimpleGraph V, DecidableRel K.Adj :=
      fun K => Classical.decRel K.Adj
    J.edgeFinset.card <= 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.connected_planar_drawing_edge_count__p2m_0951cfca_b350_4b14_85c9_9d9dc14f4b38_a3 J hJ hconn hcard