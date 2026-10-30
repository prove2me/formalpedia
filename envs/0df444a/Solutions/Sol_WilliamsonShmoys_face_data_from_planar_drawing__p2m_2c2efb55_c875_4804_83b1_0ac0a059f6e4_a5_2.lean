-- Prove2me | solution 2 for WilliamsonShmoys.face_data_from_planar_drawing__p2m_2c2efb55_c875_4804_83b1_0ac0a059f6e4_a5
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T07:05:18.062018+00:00
-- url     : https://prove2.me/submissions/6d7cba81-4548-4338-9c4f-46cfd0abb35c

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound__p2m_58a549ee_4768_4664_9403_907071b96f48_a4
import Theorems.Thm_WilliamsonShmoys_connected_edge_count_lower_bound__p2m_58a549ee_4768_4664_9403_907071b96f48_a4
import Theorems.Thm_WilliamsonShmoys_face_data_arithmetic_connected__p2m_58a549ee_4768_4664_9403_907071b96f48_a5

set_option autoImplicit false
open scoped BigOperators

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hconn : H.Connected) (hcard : 3 ≤ Fintype.card V) :
    ∃ (F : Type) (inst : Fintype F) (length : F → Nat),
      @Fintype.card V inferInstance + @Fintype.card F inst = H.edgeSet.ncard + 2 ∧
      (∀ f : F, 3 ≤ length f) ∧
      (letI : Fintype F := inst; (∑ f : F, length f) = 2 * H.edgeSet.ncard) := by
  have hlow : Fintype.card V ≤ H.edgeSet.ncard + 1 :=
    WilliamsonShmoys.connected_edge_count_lower_bound__p2m_58a549ee_4768_4664_9403_907071b96f48_a4
      H hconn
  have hupp :=
    WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_58a549ee_4768_4664_9403_907071b96f48_a4
      H hH hcard
  exact WilliamsonShmoys.face_data_arithmetic_connected__p2m_58a549ee_4768_4664_9403_907071b96f48_a5
    (Fintype.card V) H.edgeSet.ncard hcard hlow hupp