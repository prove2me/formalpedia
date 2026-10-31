-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_edge_bound__p2m_093d3833_026f_4cc9_9066_8ef7487e85b6_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T13:15:56.252688+00:00
-- url     : https://prove2.me/submissions/ad533a8b-a712-47a0-bf02-bcc99cbccff8

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib
import Theorems.Thm_WilliamsonShmoys_connected_planar_face_count_certificate__p2m_0a6cb8c8_85f4_4527_b550_0c59830e1a8e_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V)
    (hconn : G.Connected) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨f, heuler, hfaces⟩ :=
    WilliamsonShmoys.connected_planar_face_count_certificate__p2m_0a6cb8c8_85f4_4527_b550_0c59830e1a8e_a1
      G hG hV hconn
  omega