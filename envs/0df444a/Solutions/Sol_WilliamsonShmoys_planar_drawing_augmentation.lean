-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_augmentation
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T06:26:13.632011+00:00
-- url     : https://prove2.me/submissions/678ee6f2-fa98-4c9e-9553-eedf46023077

import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_extension_exists
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_cardinality

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    exists H : SimpleGraph V, M <= H /\ WilliamsonShmoys.HasPlanarDrawingOn H /\
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨H, hMH, hH, hmax⟩ :=
    WilliamsonShmoys.maximal_planar_drawing_extension_exists M hM
  exact ⟨H, hMH, hH,
    WilliamsonShmoys.maximal_planar_drawing_edge_cardinality H hV hH hmax⟩