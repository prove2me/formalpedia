-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_graph_edge_bound_ea237986_dde8_45aa_8717_82b33fafcc6c
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T11:34:09.421897+00:00
-- url     : https://prove2.me/submissions/c109c7b8-0eb2-4655-a1ec-899104be1f64
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_faceCounts
import Theorems.Thm_WilliamsonShmoys_edgeBound_of_faceCounts

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hConn : G.Connected)
    (hCard : 3 <= Fintype.card V) :
    G.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  exact WilliamsonShmoys.edgeBound_of_faceCounts G
    (WilliamsonShmoys.planarDrawingOn_faceCounts G hG hConn hCard)
