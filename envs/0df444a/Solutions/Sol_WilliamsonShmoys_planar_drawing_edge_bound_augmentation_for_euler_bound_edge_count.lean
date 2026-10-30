-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_bound_augmentation_for_euler_bound_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T18:44:34.527337+00:00
-- url     : https://prove2.me/submissions/e414f82f-206e-4c44-aaec-cc8312cc842b

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_upper_bound_for_augmentation_6371ac88_6bee_4ed8_a9a6_c374e5df5035
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_lower_bound_for_augmentation_6371ac88_6bee_4ed8_a9a6_c374e5df5035

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : forall K : SimpleGraph V, H <= K ->
      WilliamsonShmoys.HasPlanarDrawingOn K -> K <= H) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hupper :=
    WilliamsonShmoys.planar_drawing_edge_upper_bound_for_augmentation_6371ac88_6bee_4ed8_a9a6_c374e5df5035 H hV hH
  have hlower :=
    WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound_for_augmentation_6371ac88_6bee_4ed8_a9a6_c374e5df5035 H hV hH hmax
  omega