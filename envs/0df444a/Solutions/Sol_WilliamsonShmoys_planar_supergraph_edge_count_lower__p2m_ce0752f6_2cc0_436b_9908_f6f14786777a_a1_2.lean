-- Prove2me | solution 2 for WilliamsonShmoys.planar_supergraph_edge_count_lower__p2m_ce0752f6_2cc0_436b_9908_f6f14786777a_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:42:49.027772+00:00
-- url     : https://prove2.me/submissions/d43b0ede-95c1-4150-a4eb-f00729b54df3

import Theorems.Thm_WilliamsonShmoys_planar_graph_has_dense_completion__p2m_a1bc3295_288e_4dac_b293_e5c76a636381_a1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 <= Fintype.card V) :
    ∃ N : SimpleGraph V, M ≤ N ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      3 * Fintype.card V <= N.edgeSet.ncard + 6 :=
  WilliamsonShmoys.planar_graph_has_dense_completion__p2m_a1bc3295_288e_4dac_b293_e5c76a636381_a1 M hDraw hCard
