-- Prove2me | solution 2 for WilliamsonShmoys.planar_edge_count_bound__p2m_37c28fdb_a658_40e3_b030_60d915d37051_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T21:47:41.060986+00:00
-- url     : https://prove2.me/submissions/77d4f508-f640-4730-a6db-dbec24cc9bae
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_bound__p2m_7f8156d0_59cd_483d_b914_1d18d842c166_a2

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 <= Fintype.card V) :
    G.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  exact WilliamsonShmoys.planar_edge_bound__p2m_7f8156d0_59cd_483d_b914_1d18d842c166_a2 G hG hV