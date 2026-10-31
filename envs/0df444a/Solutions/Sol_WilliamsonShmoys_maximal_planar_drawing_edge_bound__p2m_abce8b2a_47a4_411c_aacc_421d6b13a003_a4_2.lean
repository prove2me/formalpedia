-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_drawing_edge_bound__p2m_abce8b2a_47a4_411c_aacc_421d6b13a003_a4
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:54:51.82662+00:00
-- url     : https://prove2.me/submissions/ab93a89b-773c-48ec-ae32-559a7eeff96a

import Theorems.Thm_WilliamsonShmoys_planar_graph_has_edge_bounded_extension_maximal_edge_bound

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K) :
    3 * Fintype.card V ≤ K.edgeSet.ncard + 6 :=
  WilliamsonShmoys.planar_graph_has_edge_bounded_extension_maximal_edge_bound K hK hV hmax
