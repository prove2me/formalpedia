-- Prove2me | solution 1 for WilliamsonShmoys.inclusionMaximalPlanarSupergraph_has_maxEdges__p2m_541725ce_ba0e_4ec7_9bf8_a3e758b67715_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T01:38:57.163228+00:00
-- url     : https://prove2.me/submissions/75c66f7c-339d-4217-8c7c-4590925b252e

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_of_card_ge_three__p2m_afb5df26_e4fb_4772_9aa3_0e4304c46b48_a1

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [hHdec : DecidableRel H.Adj]
    (hH : HasPlanarDrawingOn H)
    (hn : 3 <= Fintype.card V)
    (hmax : forall (J : SimpleGraph V) (_ : DecidableRel J.Adj),
      H <= J -> HasPlanarDrawingOn J -> J <= H) :
    3 * Fintype.card V - 6 = H.edgeFinset.card := by
  classical
  have hmax' : forall N : SimpleGraph V,
      HasPlanarDrawingOn N -> H <= N -> N = H := by
    intro N hN hsub
    have hback : N <= H := hmax N inferInstance hsub hN
    exact le_antisymm hback hsub
  have hcount :=
    WilliamsonShmoys.maximal_planar_edge_count_of_card_ge_three__p2m_afb5df26_e4fb_4772_9aa3_0e4304c46b48_a1
      H hH hmax' hn
  have hcardedge : H.edgeFinset.card = H.edgeSet.ncard := by
    rw [SimpleGraph.edgeFinset_card]
    exact Set.fintypeCard_eq_ncard H.edgeSet
  exact hcount.symm.trans hcardedge.symm
