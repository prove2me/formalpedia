-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_face_boundary_decomposition__p2m_189aab1a_280b_4ab3_961b_1c0b2454cb23_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:21:08.207844+00:00
-- url     : https://prove2.me/submissions/f85c0ef2-a1b3-42e4-9570-8f85fb4953eb

import Theorems.Thm_WilliamsonShmoys_connected_planar_face_boundary_decomposition__p2m_189aab1a_280b_4ab3_961b_1c0b2454cb23_a4

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V)
    (hconn : G.Connected) :
    ∃ f : ℕ, ∃ lengths : List ℕ,
      f + Fintype.card V = G.edgeSet.ncard + 2 ∧
      lengths.length = f ∧
      lengths.sum = 2 * G.edgeSet.ncard ∧
      ∀ x ∈ lengths, 3 ≤ x :=
  WilliamsonShmoys.connected_planar_face_boundary_decomposition__p2m_189aab1a_280b_4ab3_961b_1c0b2454cb23_a4 G hG hV hconn
