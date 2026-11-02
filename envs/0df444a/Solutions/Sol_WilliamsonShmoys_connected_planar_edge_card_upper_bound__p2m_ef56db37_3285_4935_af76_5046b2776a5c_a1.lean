-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_edge_card_upper_bound__p2m_ef56db37_3285_4935_af76_5046b2776a5c_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:33:07.267903+00:00
-- url     : https://prove2.me/submissions/3378d6e1-7529-41a4-8005-e663ddbaee8b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_drawing_face_structure__p2m_2c76ab23_aade_4532_a35e_5e2cbf29bb25_a1
import Theorems.Thm_WilliamsonShmoys_euler_face_counting_edge_bound__p2m_2c76ab23_aade_4532_a35e_5e2cbf29bb25_a1

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
    [DecidableRel K.Adj] (hcard : 3 ≤ Fintype.card V) (hconn : K.Connected)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    K.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨F, hF, hFdec, face, hEuler, hdeg, hcount⟩ :=
    WilliamsonShmoys.connected_drawing_face_structure__p2m_2c76ab23_aade_4532_a35e_5e2cbf29bb25_a1
      K hcard hconn hK
  letI : Fintype F := hF
  letI : DecidableEq F := hFdec
  exact WilliamsonShmoys.euler_face_counting_edge_bound__p2m_2c76ab23_aade_4532_a35e_5e2cbf29bb25_a1
    K F face hEuler hdeg hcount (SimpleGraph.dart_card_eq_twice_card_edges K) hcard