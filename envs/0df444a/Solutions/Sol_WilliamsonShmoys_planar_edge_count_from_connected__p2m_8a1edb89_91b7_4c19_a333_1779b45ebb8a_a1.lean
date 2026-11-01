-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_from_connected__p2m_8a1edb89_91b7_4c19_a333_1779b45ebb8a_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:22:42.363203+00:00
-- url     : https://prove2.me/submissions/189d9097-518f-4cfe-985f-41603f505d46
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_supergraph_of_planar__p2m_7851b0dc_47ad_49a3_a8e3_cfe708bc6902_a1
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_of_connected_planar_supergraph__p2m_7851b0dc_47ad_49a3_a8e3_cfe708bc6902_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hconnBound : ∀ (H : SimpleGraph V) (dH : DecidableRel H.Adj),
      H.Connected → HasPlanarDrawingOn H → 3 ≤ Fintype.card V →
      (letI : DecidableRel H.Adj := dH
       H.edgeFinset.card ≤ 3 * Fintype.card V - 6))
    (hG : HasPlanarDrawingOn G)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel G.Adj := dG
     G.edgeFinset.card ≤ 3 * Fintype.card V - 6) := by
  apply WilliamsonShmoys.planar_edge_count_of_connected_planar_supergraph__p2m_7851b0dc_47ad_49a3_a8e3_cfe708bc6902_a1
      G dG hconnBound hG hcard
  exact WilliamsonShmoys.connected_planar_supergraph_of_planar__p2m_7851b0dc_47ad_49a3_a8e3_cfe708bc6902_a1 G dG hG