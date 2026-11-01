-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_extension__p2m_52ae77ae_f85b_40f5_bd03_34373df951b6_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T20:59:09.233247+00:00
-- url     : https://prove2.me/submissions/a6933677-cf96-4632-bf2d-c4cd03c94766
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_connected_extension_of_strict_supergraph_step__p2m_8e1589da_8236_4d2f_a43b_c94137df9ddf_a1
import Theorems.Thm_WilliamsonShmoys_planar_drawing_disconnected_strict_step__p2m_8e1589da_8236_4d2f_a43b_c94137df9ddf_a1
import Mathlib

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V, K ≤ H ∧ H.Connected ∧ HasPlanarDrawingOn H := by
  apply WilliamsonShmoys.finite_connected_extension_of_strict_supergraph_step__p2m_8e1589da_8236_4d2f_a43b_c94137df9ddf_a1
    K HasPlanarDrawingOn hK
  intro H hKH hH hDisconnected
  classical
  exact WilliamsonShmoys.planar_drawing_disconnected_strict_step__p2m_8e1589da_8236_4d2f_a43b_c94137df9ddf_a1
    H hH hDisconnected