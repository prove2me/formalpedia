-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_extension__p2m_686fb965_c7d3_49a9_b66b_5594659aa3e2_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:40:48.817346+00:00
-- url     : https://prove2.me/submissions/ea4413bd-86ae-44df-ac80-40150b21ffc7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_finite_simpleGraph_property_maximal_extension__p2m_bb030fc9_0317_496e_aee9_1032f339651c_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (dH : DecidableRel H.Adj)
    (hH : HasPlanarDrawingOn H)
    (hcard : 3 <= Fintype.card V) :
    letI : DecidableRel H.Adj := dH
    Exists fun L : SimpleGraph V => Exists fun dL : DecidableRel L.Adj =>
      And (H <= L) (And (HasPlanarDrawingOn L)
      (forall (K : SimpleGraph V) (dK : DecidableRel K.Adj),
        L <= K -> HasPlanarDrawingOn K -> K = L)) := by
  letI : DecidableRel H.Adj := dH
  obtain ⟨L, hL, hPlanar, hMax⟩ :=
    WilliamsonShmoys.finite_simpleGraph_property_maximal_extension__p2m_bb030fc9_0317_496e_aee9_1032f339651c_a1
      H HasPlanarDrawingOn hH
  refine ⟨L, Classical.decRel _, hL, hPlanar, ?_⟩
  intro K dK hLK hK
  exact hMax K hLK hK