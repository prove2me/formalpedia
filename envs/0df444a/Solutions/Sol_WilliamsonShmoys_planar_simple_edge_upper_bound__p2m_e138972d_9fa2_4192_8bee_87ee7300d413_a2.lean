-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_edge_upper_bound__p2m_e138972d_9fa2_4192_8bee_87ee7300d413_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:28:32.417984+00:00
-- url     : https://prove2.me/submissions/72f30adb-7cdf-4902-8bee-cf655464aa45

import Theorems.Thm_WilliamsonShmoys_planar_edge_count_bound_retry3

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 <= Fintype.card V) :
    G.edgeSet.ncard <= 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_edge_count_bound_retry3 G hG hV
