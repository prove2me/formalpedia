-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_0d90a4e2_211c_41d9_a3e6_1089ea8087c9_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-02T22:25:34.926431+00:00
-- url     : https://prove2.me/submissions/9773e70e-c0d3-4b06-8719-d29b0939fc1a

import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count_eq_euler

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hK : HasPlanarDrawingOn K)
    (hmax : ∀ H : SimpleGraph V, K ≤ H → HasPlanarDrawingOn H → H ≤ K) :
    3 * Fintype.card V = K.edgeSet.ncard + 6 :=
  WilliamsonShmoys.maximal_drawable_graph_edge_count_eq_euler K hK hV hmax