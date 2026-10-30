-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_face_boundary_decomposition__p2m_189aab1a_280b_4ab3_961b_1c0b2454cb23_a4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T21:36:21.833196+00:00
-- url     : https://prove2.me/submissions/36387686-6c27-4dce-b9a2-98adc414b08e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_planar_connected_edge_bounds__p2m_e180e171_1461_4456_9297_ea94a0392a1c_a11
import Theorems.Thm_WilliamsonShmoys_euler_list_arithmetic__p2m_e180e171_1461_4456_9297_ea94a0392a1c_a11
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
      ∀ x ∈ lengths, 3 ≤ x := by
  have hb := WilliamsonShmoys_planar_connected_edge_bounds__p2m_e180e171_1461_4456_9297_ea94a0392a1c_a11
    G hG hV hconn
  exact WilliamsonShmoys_euler_list_arithmetic__p2m_e180e171_1461_4456_9297_ea94a0392a1c_a11
    (Fintype.card V) G.edgeSet.ncard hb.1 hb.2