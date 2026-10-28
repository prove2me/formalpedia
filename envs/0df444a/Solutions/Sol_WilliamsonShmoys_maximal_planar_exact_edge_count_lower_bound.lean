-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_exact_edge_count_lower_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T05:09:43.517383+00:00
-- url     : https://prove2.me/submissions/272b7b4d-0554-466c-9584-7a5a804a719a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_with_edge_bound

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDrawing : HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ L : SimpleGraph V, K ≤ L →
      HasPlanarDrawingOn L → L = K) :
    3 * Fintype.card V ≤ K.edgeSet.ncard + 6 := by
  obtain ⟨L, hKL, hLDrawing, hBound⟩ :=
    WilliamsonShmoys.exists_planar_supergraph_with_edge_bound K hDrawing hCard
  have hLEqK : L = K := hMax L hKL hLDrawing
  simpa [hLEqK] using hBound