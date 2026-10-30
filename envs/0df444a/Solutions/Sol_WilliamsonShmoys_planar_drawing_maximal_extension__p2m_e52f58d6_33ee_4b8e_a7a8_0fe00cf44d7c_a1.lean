-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_extension__p2m_e52f58d6_33ee_4b8e_a7a8_0fe00cf44d7c_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:55:57.530135+00:00
-- url     : https://prove2.me/submissions/da643479-4bcb-40ce-8443-ba22d180381d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_maximal_supergraph__p2m_b48f5d89_dd8c_44de_b172_78fd0037e2dc_a1
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hconn : K.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ (H : SimpleGraph V) (dH : DecidableRel H.Adj),
      (letI : DecidableRel H.Adj := dH
       K ≤ H ∧ H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
       (∀ (L : SimpleGraph V) (dL : DecidableRel L.Adj),
         (letI : DecidableRel L.Adj := dL
          H ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ H)) ∧
       K.edgeFinset.card ≤ H.edgeFinset.card) := by
  exact WilliamsonShmoys.finite_maximal_supergraph__p2m_b48f5d89_dd8c_44de_b172_78fd0037e2dc_a1
    K WilliamsonShmoys.HasPlanarDrawingOn hK hconn