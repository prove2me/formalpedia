-- Prove2me | solution 1 for WilliamsonShmoys_planar_drawing_maximal_extension__p2m_e8e38ca1_7bc9_4d8d_a468_0001acb809e9_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:45:33.038198+00:00
-- url     : https://prove2.me/submissions/875a4def-0bda-4983-a4f9-2793f453ddf1

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_exists_maximal_feasible_extension_finite__p2m_53772a33_25fb_4be5_bc25_56c0a0bf34f9_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    (hcard : 3 <= Fintype.card V) :
    ∃ H : SimpleGraph V, G ≤ H ∧ HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K ≤ H := by
  exact exists_maximal_feasible_extension_finite__p2m_53772a33_25fb_4be5_bc25_56c0a0bf34f9_a1
    (P := HasPlanarDrawingOn) G hG