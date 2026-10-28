-- Prove2me | solution 1 for WilliamsonShmoys.connected_simple_planar_edge_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T16:57:26.476998+00:00
-- url     : https://prove2.me/submissions/a9c75ddb-3b18-45cd-bc1d-e3fdb5971c2d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_WilliamsonShmoys_PlanarEulerData
import Theorems.Thm_WilliamsonShmoys_hasPlanarDrawingOn_eulerData
import Theorems.Thm_WilliamsonShmoys_planarEulerData_edgeBound

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hconn : G.Connected)
    (hV : 3 <= Fintype.card V) :
    G.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  let data := Classical.choice
    (WilliamsonShmoys.hasPlanarDrawingOn_eulerData G hdraw hconn hV)
  exact WilliamsonShmoys.planarEulerData_edgeBound G data hV