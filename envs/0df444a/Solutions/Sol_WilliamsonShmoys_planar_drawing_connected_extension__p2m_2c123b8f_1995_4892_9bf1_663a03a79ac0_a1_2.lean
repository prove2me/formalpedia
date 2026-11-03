-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_connected_extension__p2m_2c123b8f_1995_4892_9bf1_663a03a79ac0_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T16:09:32.389254+00:00
-- url     : https://prove2.me/submissions/677f6c63-d795-4044-b0e9-309d74352127

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_components_connected_extension__p2m_9f456864_72ae_4080_90f1_6ccbf874f47a_a2

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ T : SimpleGraph V, L ≤ T ∧ T.Connected ∧ HasPlanarDrawingOn T := by
  exact WilliamsonShmoys.planar_drawing_components_connected_extension__p2m_9f456864_72ae_4080_90f1_6ccbf874f47a_a2 L hL hcard
