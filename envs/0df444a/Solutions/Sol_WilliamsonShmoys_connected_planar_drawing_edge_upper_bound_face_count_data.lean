-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_drawing_edge_upper_bound_face_count_data
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T10:17:17.154285+00:00
-- url     : https://prove2.me/submissions/763d3b90-1536-4732-977b-e285341f7fcf
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_edge_upper_bound_face_count_data_connected_edge_lower_bound
import Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_edge_upper_bound_face_count_data_planar_edge_bound_for_face_count_data
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hconn : K.Connected) :
    ∃ f : ℕ,
      Fintype.card V + f = K.edgeSet.ncard + 2 ∧
      3 * f <= 2 * K.edgeSet.ncard := by
  let n := Fintype.card V
  let m := K.edgeSet.ncard
  have hlo : n <= m + 1 :=
    WilliamsonShmoys.connected_planar_drawing_edge_upper_bound_face_count_data_connected_edge_lower_bound K hconn
  have hup : m <= 3 * n - 6 :=
    WilliamsonShmoys.connected_planar_drawing_edge_upper_bound_face_count_data_planar_edge_bound_for_face_count_data K hV hK hconn
  have hup' : m + 6 <= 3 * n := by omega
  have hn : n <= m + 2 := by omega
  let f := m + 2 - n
  have hfn : f + n = m + 2 := by
    dsimp [f]
    exact Nat.sub_add_cancel hn
  refine ⟨f, ?_, ?_⟩
  · change n + f = m + 2
    omega
  · change 3 * f <= 2 * m
    omega
