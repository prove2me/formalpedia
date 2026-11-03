-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_bound__p2m_1869d2b3_4acb_4df1_b926_664515403053_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T11:59:34.220012+00:00
-- url     : https://prove2.me/submissions/d42aa1b5-1b53-4d3a-ae67-86573d872d6a

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_graph_edge_bound__p2m_26fdce0d_6688_44e7_929e_c61ea3cc0bd1_a2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax :
      ∀ K : SimpleGraph V,
        (∀ u v, H.Adj u v → K.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn K →
        ∀ u v, K.Adj u v → H.Adj u v) :
    (letI : DecidableRel H.Adj := Classical.decRel H.Adj
     H.edgeFinset.card + 6 ≤ 3 * Fintype.card V) := by
  exact WilliamsonShmoys.planar_graph_edge_bound__p2m_26fdce0d_6688_44e7_929e_c61ea3cc0bd1_a2
    H hcard hdraw