-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_extension__p2m_33fd9cf6_5dff_42ab_8e0f_e49b055267c2_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T02:41:25.397137+00:00
-- url     : https://prove2.me/submissions/0fb5bf4d-8dfc-4b55-ba37-8527bbc10339

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_285fd92f_ac7f_4984_a234_6720989533e3_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H)
    (hcard : 3 <= Fintype.card V) :
    Exists fun K : SimpleGraph V =>
      And (LE.le H K) (And (HasPlanarDrawingOn K)
        (letI : DecidableRel K.Adj := Classical.decRel _;
         3 * Fintype.card V - 6 <= K.edgeFinset.card)) := by
  classical
  have hExt :=
    WilliamsonShmoys.planar_triangulation_extension__p2m_285fd92f_ac7f_4984_a234_6720989533e3_a2
      H hcard hH
  let K : SimpleGraph V := Classical.choose hExt
  have hHK : H <= K := (Classical.choose_spec hExt).1
  have hK : HasPlanarDrawingOn K := (Classical.choose_spec hExt).2.1
  have hcount :
      3 * Fintype.card V = K.edgeFinset.card + 6 :=
    (Classical.choose_spec hExt).2.2
  refine Exists.intro K (And.intro hHK (And.intro hK ?_))
  letI : DecidableRel K.Adj := Classical.decRel _
  omega
