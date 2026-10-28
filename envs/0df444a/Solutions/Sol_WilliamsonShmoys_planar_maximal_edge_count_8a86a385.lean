-- Prove2me | solution 1 for WilliamsonShmoys.planar_maximal_edge_count_8a86a385
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T13:50:23.488031+00:00
-- url     : https://prove2.me/submissions/1f3b5bf5-797d-4b08-80e9-567bb84ad918
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_9064c577
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound_9064c577

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hConn : H.Connected)
    (hDraw : HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hUpper := WilliamsonShmoys.planar_edge_count_upper_bound_9064c577
    H hConn hDraw hCard
  have hLower := WilliamsonShmoys.maximal_planar_edge_count_lower_bound_9064c577
    H hConn hDraw hCard hMax
  omega