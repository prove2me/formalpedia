-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_euler_certificate__p2m_844ee2d0_ef82_4c36_8373_ea0ee656ba91_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T15:59:45.026195+00:00
-- url     : https://prove2.me/submissions/c42ed79d-8a23-47e3-b4d2-fc3d87ab8615

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound__p2m_e37f737c_f285_4a30_83a0_16b070403a61_a2
import Theorems.Thm_WilliamsonShmoys_supergraph_euler_certificate_of_edge_bound__p2m_e37f737c_f285_4a30_83a0_16b070403a61_a2

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hGdraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ (H : SimpleGraph V) (f : ℕ),
      G ≤ H ∧
      (letI : DecidableRel G.Adj := Classical.decRel G.Adj
       letI : DecidableRel H.Adj := Classical.decRel H.Adj
       G.edgeFinset.card ≤ H.edgeFinset.card) ∧
      (letI : DecidableRel H.Adj := Classical.decRel H.Adj
       Fintype.card V + f = H.edgeFinset.card + 2) ∧
      (letI : DecidableRel H.Adj := Classical.decRel H.Adj
       3 * f ≤ 2 * H.edgeFinset.card) := by
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  have hbound : G.edgeFinset.card ≤ 3 * Fintype.card V - 6 :=
    WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_e37f737c_f285_4a30_83a0_16b070403a61_a2
      G hGdraw hcard
  exact
    WilliamsonShmoys.supergraph_euler_certificate_of_edge_bound__p2m_e37f737c_f285_4a30_83a0_16b070403a61_a2
      G hcard hbound