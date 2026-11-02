-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_extension__p2m_f922730b_ca22_4588_ba9a_35deaa5a3fb1_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:10:53.714612+00:00
-- url     : https://prove2.me/submissions/48fe9a2a-a644-4f24-a5e2-37cdd85efac8

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_predicate_maximal_extension__p2m_6802ab23_a3ac_43c6_8aa9_163dea1542b1_a1
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G) :
    Exists fun H : SimpleGraph V =>
      G <= H /\ HasPlanarDrawingOn H /\
        (forall K : SimpleGraph V, H <= K -> HasPlanarDrawingOn K -> K = H) := by
  exact WilliamsonShmoys.finite_predicate_maximal_extension__p2m_6802ab23_a3ac_43c6_8aa9_163dea1542b1_a1
    (P := HasPlanarDrawingOn) G hG