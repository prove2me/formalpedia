-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound__p2m_84f2d88d_c1bb_48f4_b85d_8d668d11d624_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:45:24.318562+00:00
-- url     : https://prove2.me/submissions/953c7d12-454c-4aca-88c8-ebfb7d3a5dc8

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_face_count__p2m_aad1f7a7_a04a_47ce_bdaf_91f7c06a5480_a1

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N = M) :
    3 * Fintype.card V ≤ M.edgeSet.ncard + 6 := by
  obtain ⟨f, hEuler, hFaces⟩ :=
    WilliamsonShmoys.maximal_planar_drawing_face_count__p2m_aad1f7a7_a04a_47ce_bdaf_91f7c06a5480_a1
      M hM hCard hMax
  omega