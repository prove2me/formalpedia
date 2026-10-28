-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_maximal_lower_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T05:02:57.09698+00:00
-- url     : https://prove2.me/submissions/e0028850-a930-4e2a-b2fd-650ea15c6b85
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_augmentation_6c0819c8_795c_411a_aacd_f8cf4c691759

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : HasPlanarDrawingOn T)
    (hCard : 3 ≤ Fintype.card V)
    (hmax : ∀ U : SimpleGraph V, HasPlanarDrawingOn U →
      (∀ u v, T.Adj u v → U.Adj u v) → U = T) :
    3 * Fintype.card V ≤ T.edgeSet.ncard + 6 := by
  obtain ⟨U, hU, hTU, hbound⟩ :=
    WilliamsonShmoys.maximal_planar_edge_count_augmentation_6c0819c8_795c_411a_aacd_f8cf4c691759 T hT hCard
  have hEq : U = T := hmax U hU hTU
  simpa only [hEq] using hbound