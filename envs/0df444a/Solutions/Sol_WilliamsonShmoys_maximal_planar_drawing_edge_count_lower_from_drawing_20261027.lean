-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_from_drawing_20261027
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T04:03:41.766616+00:00
-- url     : https://prove2.me/submissions/7704ff45-1e14-4b01-91a1-0389841cbbd8

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_augmentation_20261028

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ K : SimpleGraph V,
      G ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ G) :
    3 * (Fintype.card V : Int) - 6 ≤ (G.edgeSet.ncard : Int) := by
  obtain ⟨K, hSub, hK, hCount⟩ :=
    WilliamsonShmoys.maximal_planar_drawing_augmentation_20261028 G hG hCard
  have hBack : K ≤ G := hMax K hSub hK
  have hEq : K = G := le_antisymm hBack hSub
  rw [hEq] at hCount
  omega