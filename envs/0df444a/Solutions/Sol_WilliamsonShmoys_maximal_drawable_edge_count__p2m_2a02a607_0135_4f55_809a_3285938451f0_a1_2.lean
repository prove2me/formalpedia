-- Prove2me | solution 2 for WilliamsonShmoys.maximal_drawable_edge_count__p2m_2a02a607_0135_4f55_809a_3285938451f0_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:33:19.581976+00:00
-- url     : https://prove2.me/submissions/7c50290a-0b55-486e-90d7-15d3a08ecb57

import Theorems.Thm_WilliamsonShmoys_edge_count_of_edge_maximal_drawable_graph

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L) (hCard : 3 ≤ Fintype.card V) (hmax : ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L) : L.edgeSet.ncard = 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.edge_count_of_edge_maximal_drawable_graph L hL hCard hmax
