-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_lower_bound_c76468fe
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T20:12:33.140866+00:00
-- url     : https://prove2.me/submissions/aab03eb8-0d1f-4bb8-8c48-edbee3de7c39
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_face_count_c76468fe

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ H.edgeSet.ncard + 6 := by
  obtain ⟨f, hEuler, hTriangular⟩ :=
    WilliamsonShmoys.maximal_planar_edge_face_count_c76468fe H hH hmax hCard
  omega