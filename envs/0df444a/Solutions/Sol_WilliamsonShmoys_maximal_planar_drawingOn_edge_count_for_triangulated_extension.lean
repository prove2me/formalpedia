-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawingOn_edge_count_for_triangulated_extension
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T17:07:58.944228+00:00
-- url     : https://prove2.me/submissions/924dec96-ffd1-4969-aa07-99020c4b4031
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_extension_with_euler_edge_count

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ L : SimpleGraph V, K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨L, hKL, hLDraw, hCount⟩ :=
    WilliamsonShmoys.planar_extension_with_euler_edge_count K hDraw hCard
  have hLK : L = K := hMax L hKL hLDraw
  simpa [hLK] using hCount