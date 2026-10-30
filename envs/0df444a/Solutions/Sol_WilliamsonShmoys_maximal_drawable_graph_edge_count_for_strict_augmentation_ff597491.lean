-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_edge_count_for_strict_augmentation_ff597491
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T17:18:25.817809+00:00
-- url     : https://prove2.me/submissions/44bf5613-0bad-4e37-8eaa-a2c4a17b3eb7

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_completion_edge_count_ff597491
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V) (hUdraw : WilliamsonShmoys.HasPlanarDrawingOn U)
    (hCard : 3 ≤ Fintype.card V)
    (hUmax : ∀ W : SimpleGraph V, U ≤ W →
      WilliamsonShmoys.HasPlanarDrawingOn W → W = U) :
    U.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨H, hUH, hHdraw, hHcount⟩ :=
    WilliamsonShmoys.planar_completion_edge_count_ff597491 U hUdraw hCard
  have hHU : H = U := hUmax H hUH hHdraw
  simpa [hHU] using hHcount