-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_maximal_drawable_extension__p2m_64f9a932_9abc_4892_8345_6d855cf8c7f4_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:03:49.794848+00:00
-- url     : https://prove2.me/submissions/fbf10e98-11b9-41d5-9da5-c927403ce181

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_finite_hereditary_graph_property_has_maximal_extension__p2m_70f84f17_dac3_4815_92df_56beadc09612_a2
import Theorems.Thm_WilliamsonShmoys_hasPlanarDrawingOn_mono__p2m_70f84f17_dac3_4815_92df_56beadc09612_a2

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hN : HasPlanarDrawingOn N) :
    ∃ K : SimpleGraph V, N ≤ K ∧ HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L ≤ K := by
  exact WilliamsonShmoys.finite_hereditary_graph_property_has_maximal_extension__p2m_70f84f17_dac3_4815_92df_56beadc09612_a2
    N HasPlanarDrawingOn hN
    (by
      intro G H hHG hG
      exact WilliamsonShmoys.hasPlanarDrawingOn_mono__p2m_70f84f17_dac3_4815_92df_56beadc09612_a2 hHG hG)