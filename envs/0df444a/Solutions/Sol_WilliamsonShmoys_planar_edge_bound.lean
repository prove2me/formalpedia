-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T20:45:40.643428+00:00
-- url     : https://prove2.me/submissions/29533ae2-65d5-472c-bca2-438645727f12
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_bound_connected
import Theorems.Thm_WilliamsonShmoys_planar_connected_extension

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    M.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨N, hMN, hconn, hN, hcard⟩ :=
    WilliamsonShmoys.planar_connected_extension M hV hM
  exact le_trans hcard
    (WilliamsonShmoys.planar_edge_bound_connected N hV hconn hN)