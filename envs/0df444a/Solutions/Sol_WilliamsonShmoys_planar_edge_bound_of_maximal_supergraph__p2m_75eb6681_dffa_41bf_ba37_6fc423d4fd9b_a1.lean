-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_bound_of_maximal_supergraph__p2m_75eb6681_dffa_41bf_ba37_6fc423d4fd9b_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:54:30.224088+00:00
-- url     : https://prove2.me/submissions/1570a292-de41-456a-9239-d929a0e9d875

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_restrict_subgraph__p2m_6d91b10d_a30f_4f1a_8acb_96a7ed12e6b9_a1
import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound__p2m_6d91b10d_a30f_4f1a_8acb_96a7ed12e6b9_a1

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M N : SimpleGraph V)
    (hMN : M ≤ N)
    (hNdraw : HasPlanarDrawingOn N)
    (hmax : ∀ N' : SimpleGraph V, M ≤ N' → HasPlanarDrawingOn N' →
      (letI : DecidableRel N'.Adj := Classical.decRel N'.Adj
       N'.edgeFinset.card) ≤
      (letI : DecidableRel N.Adj := Classical.decRel N.Adj
       N.edgeFinset.card))
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel M.Adj := Classical.decRel M.Adj
     M.edgeFinset.card) + 6 ≤ 3 * Fintype.card V := by
  have hMdraw : HasPlanarDrawingOn M :=
    WilliamsonShmoys.planar_drawing_restrict_subgraph__p2m_6d91b10d_a30f_4f1a_8acb_96a7ed12e6b9_a1
      M N hMN hNdraw
  exact WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_6d91b10d_a30f_4f1a_8acb_96a7ed12e6b9_a1
    M hMdraw hcard