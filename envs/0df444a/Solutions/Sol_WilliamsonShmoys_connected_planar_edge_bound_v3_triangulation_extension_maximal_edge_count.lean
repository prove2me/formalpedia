-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_edge_bound_v3_triangulation_extension_maximal_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T16:41:26.678859+00:00
-- url     : https://prove2.me/submissions/26b43229-55dd-4066-9a45-c41cb13316f6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_augmentation_edge_count_fixed_vertices

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hMax : ∀ L : SimpleGraph V,
      K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨L, hKL, hDrawL, hCount⟩ :=
    WilliamsonShmoys.planar_augmentation_edge_count_fixed_vertices K hV hDraw
  have hLK : L ≤ K := hMax L hKL hDrawL
  have hEq : K = L := le_antisymm hKL hLK
  simpa [hEq] using hCount