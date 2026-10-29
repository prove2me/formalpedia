-- Prove2me | solution 1 for WilliamsonShmoys.face_data_from_planar_drawing__p2m_2c2efb55_c875_4804_83b1_0ac0a059f6e4_a5
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T05:54:13.799694+00:00
-- url     : https://prove2.me/submissions/6cfd5547-3c25-4be1-a09a-288fdd3ce2fa
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound__p2m_58a549ee_4768_4664_9403_907071b96f48_a4
import Theorems.Thm_WilliamsonShmoys_connected_edge_count_lower_bound__p2m_58a549ee_4768_4664_9403_907071b96f48_a4
import Theorems.Thm_WilliamsonShmoys_face_data_arithmetic__p2m_58a549ee_4768_4664_9403_907071b96f48_a4

set_option autoImplicit false
open scoped BigOperators

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hconn : H.Connected) (hcard : 3 ≤ Fintype.card V) :
    ∃ (F : Type) (inst : Fintype F) (length : F → Nat),
      @Fintype.card V inferInstance + @Fintype.card F inst = H.edgeSet.ncard + 2 ∧
      (∀ f : F, 3 ≤ length f) ∧
      (letI : Fintype F := inst; (∑ f : F, length f) = 2 * H.edgeSet.ncard) := by
  have hlow : Fintype.card V ≤ H.edgeSet.ncard + 2 := by
    have hconnEdges :=
      WilliamsonShmoys.connected_edge_count_lower_bound__p2m_58a549ee_4768_4664_9403_907071b96f48_a4
        H hconn
    omega
  have hupp :=
    WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_58a549ee_4768_4664_9403_907071b96f48_a4
      H hH hcard
  exact WilliamsonShmoys.face_data_arithmetic__p2m_58a549ee_4768_4664_9403_907071b96f48_a4
    (Fintype.card V) H.edgeSet.ncard hcard hlow hupp
