-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_bound_9064c577
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T14:50:03.101181+00:00
-- url     : https://prove2.me/submissions/42c92135-1bde-45b2-8340-8ac8d4dbd4a9

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound_from_drawing_9064c577

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hConn : K.Connected)
    (hDraw : HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ L : SimpleGraph V,
      (∀ ⦃u v⦄, K.Adj u v → L.Adj u v) →
      HasPlanarDrawingOn L →
      ∀ ⦃u v⦄, L.Adj u v → K.Adj u v) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  exact WilliamsonShmoys.planar_drawing_edge_bound_from_drawing_9064c577 K hDraw hCard