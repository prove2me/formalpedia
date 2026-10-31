-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_face_boundary_decomposition__p2m_189aab1a_280b_4ab3_961b_1c0b2454cb23_a3
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:20:51.074671+00:00
-- url     : https://prove2.me/submissions/3a107161-6b16-43bd-ade5-6674a8b53cc9

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
