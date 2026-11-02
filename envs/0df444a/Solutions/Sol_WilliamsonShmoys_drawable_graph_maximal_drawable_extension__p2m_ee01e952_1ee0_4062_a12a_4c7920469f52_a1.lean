-- Prove2me | solution 1 for WilliamsonShmoys.drawable_graph_maximal_drawable_extension__p2m_ee01e952_1ee0_4062_a12a_4c7920469f52_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:45:48.548575+00:00
-- url     : https://prove2.me/submissions/51f3462c-c8bd-4c3c-a9aa-fe564438419b

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_graph_property_maximal_extension__p2m_aafbf6a1_f3ed_41ff_93d8_51adc42299ad_a1
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G) :
    ∃ M : SimpleGraph V, G ≤ M ∧ HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N = M := by
  exact WilliamsonShmoys.finite_graph_property_maximal_extension__p2m_aafbf6a1_f3ed_41ff_93d8_51adc42299ad_a1
    HasPlanarDrawingOn G hG