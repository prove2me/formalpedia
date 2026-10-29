-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_maximal_extension__p2m_638a1f84_48cf_416d_8d32_57bed5d6bb46_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T18:49:03.110426+00:00
-- url     : https://prove2.me/submissions/9c29c81f-e9c5-408a-9be3-39177317d1b9

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_extension_of_downward_closed__p2m_b230c174_4dc5_4f1c_a300_93827e81df10_a1
import Theorems.Thm_WilliamsonShmoys_planar_drawing_subgraph__p2m_b230c174_4dc5_4f1c_a300_93827e81df10_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L) :
    ∃ K : SimpleGraph V,
      L ≤ K ∧ HasPlanarDrawingOn K ∧
      ∀ H : SimpleGraph V, K ≤ H → HasPlanarDrawingOn H → H = K := by
  exact exists_maximal_extension_of_downward_closed__p2m_b230c174_4dc5_4f1c_a300_93827e81df10_a1
    HasPlanarDrawingOn
    (by
      intro G H hGH hH
      exact planar_drawing_subgraph__p2m_b230c174_4dc5_4f1c_a300_93827e81df10_a1 hGH hH)
    L hL
