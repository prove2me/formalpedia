-- Prove2me | solution 2 for WilliamsonShmoys.planar_supergraph_triangulation__p2m_75785758_9f27_4736_ab49_77b09febfcc3_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:43:37.055423+00:00
-- url     : https://prove2.me/submissions/1cee39b8-3f28-40a4-bf2b-b61f6b3f2536

import Theorems.Thm_WilliamsonShmoys_planar_graph_triangulation_augmentation

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 <= Fintype.card V) :
    ∃ H : SimpleGraph V, K <= H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      3 * Fintype.card V = H.edgeSet.ncard + 6 :=
  WilliamsonShmoys.planar_graph_triangulation_augmentation K hK hV
