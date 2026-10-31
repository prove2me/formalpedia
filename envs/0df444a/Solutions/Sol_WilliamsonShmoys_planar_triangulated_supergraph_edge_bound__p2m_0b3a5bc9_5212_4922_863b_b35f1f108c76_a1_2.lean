-- Prove2me | solution 2 for WilliamsonShmoys.planar_triangulated_supergraph_edge_bound__p2m_0b3a5bc9_5212_4922_863b_b35f1f108c76_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:43:46.262373+00:00
-- url     : https://prove2.me/submissions/92db1862-c5c8-410f-95c3-b00f0ae9ace0

import Theorems.Thm_WilliamsonShmoys_drawable_supergraph_edge_bound

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, H ≤ K ∧ HasPlanarDrawingOn K ∧
      3 * Fintype.card V ≤ K.edgeSet.ncard + 6 :=
  WilliamsonShmoys.drawable_supergraph_edge_bound H hH hCard
