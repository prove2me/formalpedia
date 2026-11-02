-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_75eb6681_dffa_41bf_ba37_6fc423d4fd9b_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:54:37.172771+00:00
-- url     : https://prove2.me/submissions/d844e617-a1a4-4c84-b047-fd40c61781aa

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_graph_max_edge_supergraph__p2m_ec2412ad_17a6_418f_a499_5de65dee72a0_a1

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hMdraw : HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V, M ≤ N ∧ HasPlanarDrawingOn N ∧
      ∀ N' : SimpleGraph V, M ≤ N' → HasPlanarDrawingOn N' →
        (letI : DecidableRel N'.Adj := Classical.decRel N'.Adj
         N'.edgeFinset.card) ≤
        (letI : DecidableRel N.Adj := Classical.decRel N.Adj
         N.edgeFinset.card) := by
  classical
  exact WilliamsonShmoys.finite_graph_max_edge_supergraph__p2m_ec2412ad_17a6_418f_a499_5de65dee72a0_a1
    M HasPlanarDrawingOn hMdraw
