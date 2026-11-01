-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_graph_exact_edge_count__p2m_05cc95b8_6993_44ac_b777_7a2cce137e12_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-01T05:15:48.789993+00:00
-- url     : https://prove2.me/submissions/64578c23-fc22-4775-8acb-3c78416e6a38

import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_1794ae85_4ddf_4fc1_b226_9d54b8be81b3
import Mathlib

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open scoped BigOperators

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V, M ≤ N →
      WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M) :
    M.edgeSet.ncard = 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.maximal_planar_drawing_edge_count_1794ae85_4ddf_4fc1_b226_9d54b8be81b3 M hM hcard hmax
