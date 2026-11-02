-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_dcda2b2e_bb79_4b65_906a_4b43dfb1e747_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T01:06:04.558215+00:00
-- url     : https://prove2.me/submissions/2e989643-91ec-49b6-b0b1-5b12dfa76a87

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_2094dec4_72bc_4506_8cb1_28494e96e3ad_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hN : HasPlanarDrawingOn N)
    (hmax : ∀ P : SimpleGraph V, N ≤ P → HasPlanarDrawingOn P → P = N)
    (hconn : N.Connected) :
    (letI : DecidableRel N.Adj := Classical.decRel N.Adj
     3 * Fintype.card V - 6 ≤ N.edgeFinset.card) := by
  letI : DecidableRel N.Adj := Classical.decRel N.Adj
  have hbound :
      3 * Fintype.card V ≤ N.edgeSet.ncard + 6 :=
    WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_2094dec4_72bc_4506_8cb1_28494e96e3ad_a1
      N hcard hconn hN hmax
  have hcount : N.edgeSet.ncard = N.edgeFinset.card := by
    rw [← Set.fintypeCard_eq_ncard]
    exact SimpleGraph.card_edgeSet
  omega