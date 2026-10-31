-- Prove2me | solution 1 for WilliamsonShmoys.planar_completion_edge_bound__p2m_a676df72_8370_487d_8148_6fb0674d69c1_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:49:40.498575+00:00
-- url     : https://prove2.me/submissions/fca385a2-6f2d-424c-9392-548ded366b0a

import Theorems.Thm_WilliamsonShmoys_planar_graph_augment_edge_bound

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M)
    (hV : 3 <= Fintype.card V) :
    Exists fun N : SimpleGraph V => M <= N /\ HasPlanarDrawingOn N /\
      3 * Fintype.card V <= N.edgeSet.ncard + 6 :=
  WilliamsonShmoys.planar_graph_augment_edge_bound M hM hV
