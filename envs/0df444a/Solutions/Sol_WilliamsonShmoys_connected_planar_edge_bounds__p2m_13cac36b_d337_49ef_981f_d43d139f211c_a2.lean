-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_edge_bounds__p2m_13cac36b_d337_49ef_981f_d43d139f211c_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:24:54.714116+00:00
-- url     : https://prove2.me/submissions/edf4757f-eba0-45ae-b2ba-1128aadaf28c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_connected_edge_lower_bound__p2m_961b854d_f4cc_4b36_ad05_39668b153494_a2
import Theorems.Thm_WilliamsonShmoys_planar_face_count_certificate__p2m_961b854d_f4cc_4b36_ad05_39668b153494_a2

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hV : 3 ≤ Fintype.card V)
    (hconn : K.Connected)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    Fintype.card V ≤ K.edgeFinset.card + 1 ∧
      K.edgeFinset.card + 6 ≤ 3 * Fintype.card V := by
  constructor
  · exact WilliamsonShmoys.connected_edge_lower_bound__p2m_961b854d_f4cc_4b36_ad05_39668b153494_a2 K hconn
  · obtain ⟨F, faceLength, hEuler, hSum, hLength⟩ :=
      WilliamsonShmoys.planar_face_count_certificate__p2m_961b854d_f4cc_4b36_ad05_39668b153494_a2
        K hV hconn hK
    have hFaces : 3 * F ≤ 2 * K.edgeFinset.card := by
      calc
        3 * F = F * 3 := Nat.mul_comm _ _
        _ = ∑ i : Fin F, 3 := by simp
        _ ≤ ∑ i : Fin F, faceLength i := Finset.sum_le_sum fun i _ => hLength i
        _ = 2 * K.edgeFinset.card := hSum
    omega