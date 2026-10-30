-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_edge_count_repair_543ac5d4_edge_lower
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T06:30:03.691405+00:00
-- url     : https://prove2.me/submissions/1d6a6dd2-c4d8-4f49-979c-98cec030ed8b

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_augmentation_edge_lower

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hU : WilliamsonShmoys.HasPlanarDrawingOn U)
    (hmax : ∀ W : SimpleGraph V,
      U <= W →
      WilliamsonShmoys.HasPlanarDrawingOn W →
      W = U) :
    3 * Fintype.card V <= U.edgeSet.ncard + 6 := by
  obtain ⟨W, hUW, hW, hbound⟩ :=
    WilliamsonShmoys.planar_drawing_augmentation_edge_lower U hV hU
  have hEq : W = U := hmax W hUW hW
  rw [hEq] at hbound
  exact hbound