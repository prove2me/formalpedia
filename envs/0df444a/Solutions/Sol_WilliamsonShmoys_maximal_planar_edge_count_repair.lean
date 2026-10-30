-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_repair
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T17:09:48.498694+00:00
-- url     : https://prove2.me/submissions/7809df57-6ebf-4d97-aa50-64842b23024d

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_bound_augmentation_1a9e3423_67b8_4196_8909_cc8d9eac42a0

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hTdraw : WilliamsonShmoys.HasPlanarDrawingOn T)
    (hCard : 3 ≤ Fintype.card V)
    (hmax : ∀ U : SimpleGraph V, T ≤ U →
      WilliamsonShmoys.HasPlanarDrawingOn U → U = T) :
    3 * Fintype.card V ≤ T.edgeSet.ncard + 6 := by
  obtain ⟨U, hTU, hUdraw, hUbound⟩ :=
    WilliamsonShmoys.maximal_planar_edge_bound_augmentation_1a9e3423_67b8_4196_8909_cc8d9eac42a0
      T hTdraw hCard
  have hUT : U = T := hmax U hTU hUdraw
  simpa only [hUT] using hUbound