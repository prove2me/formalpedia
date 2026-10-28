-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawingOn_exact_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T12:09:54.020981+00:00
-- url     : https://prove2.me/submissions/4a4b01a8-26e0-4d5f-a4b7-34cc5ce1ee31
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edgeSet_ncard_le
import Theorems.Thm_WilliamsonShmoys_planar_maximal_edgeSet_ncard_ge

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : HasPlanarDrawingOn L)
    (hconn : L.Connected)
    (hmax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M ≤ L) :
    3 * Fintype.card V - 6 = L.edgeSet.ncard := by
  have hupper : L.edgeSet.ncard ≤ 3 * Fintype.card V - 6 :=
    WilliamsonShmoys.planar_edgeSet_ncard_le L hV hL hconn
  have hlower : 3 * Fintype.card V - 6 ≤ L.edgeSet.ncard :=
    WilliamsonShmoys.planar_maximal_edgeSet_ncard_ge L hV hL hconn hmax
  omega