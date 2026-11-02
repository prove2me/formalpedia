-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_supergraph__p2m_0d510956_7da0_4290_84d6_372bf969c07f_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T15:34:18.665975+00:00
-- url     : https://prove2.me/submissions/8eba1d38-18ed-47d1-8857-3199311cb682

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_edge_maximal__p2m_03cdb16c_d4b2_4cf3_b4f1_33da613ee6f7_a1
import Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_supergraph_connected__p2m_03cdb16c_d4b2_4cf3_b4f1_33da613ee6f7_a1
import Mathlib

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hM : HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V, M ≤ N ∧ N.Connected ∧ HasPlanarDrawingOn N ∧
      (letI : DecidableRel M.Adj := Classical.decRel M.Adj
       letI : DecidableRel N.Adj := Classical.decRel N.Adj
       M.edgeFinset.card ≤ N.edgeFinset.card) := by
  obtain ⟨N, hMN, hN, hmax⟩ :=
    WilliamsonShmoys.planar_supergraph_edge_maximal__p2m_03cdb16c_d4b2_4cf3_b4f1_33da613ee6f7_a1
      M hV hM
  have hconn :=
    WilliamsonShmoys.edge_maximal_planar_supergraph_connected__p2m_03cdb16c_d4b2_4cf3_b4f1_33da613ee6f7_a1
      M N hV hM hMN hN hmax
  refine ⟨N, hMN, hconn, hN, ?_⟩
  exact hmax M le_rfl hM