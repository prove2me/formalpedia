-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_repair_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T04:07:15.246556+00:00
-- url     : https://prove2.me/submissions/71f8f0a4-1dea-4db6-b7cf-146e60757efe
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_exists
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ L : SimpleGraph V, K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    3 * Fintype.card V = K.edgeSet.ncard + 6 := by
  obtain ⟨T, hKT, hTdraw, hTcard⟩ :=
    WilliamsonShmoys.planar_triangulation_exists (V := V) K hcard
  have hTK : T = K := hmax T hKT hTdraw
  simpa [hTK] using hTcard