-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_4881293e_7bf5_4184_9f0b_57a8f75b0b6d
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T04:10:05.125249+00:00
-- url     : https://prove2.me/submissions/d3d52ca6-64de-43df-ab46-d79d02aadcf2

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_augmentation_exact_edge_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T)
    (hV : 3 <= Fintype.card V)
    (hMax : ∀ U : SimpleGraph V,
      T ≤ U → WilliamsonShmoys.HasPlanarDrawingOn U → U ≤ T) :
    T.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨U, hTU, hU, hCount⟩ :=
    WilliamsonShmoys.planar_drawing_augmentation_exact_edge_count T hT hV
  have hUT : U ≤ T := hMax U hTU hU
  have hEq : T = U := le_antisymm hTU hUT
  simpa [hEq] using hCount