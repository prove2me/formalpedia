-- Prove2me | solution 1 for WilliamsonShmoys.planar_finite_edge_maximal_extension__p2m_d847cb0d_bf38_465c_a743_e30e146fb79e_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:20:16.118404+00:00
-- url     : https://prove2.me/submissions/1d10f5a1-168c-4e89-bf9d-822b7e90d247

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_supergraph_card_maximal__p2m_67fa8ed9_e0b5_4d6e_a654_f64162c7a789_a1
import Mathlib

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H) :
    exists K : SimpleGraph V,
      H <= K /\ HasPlanarDrawingOn K /\
      (letI : DecidableRel H.Adj := Classical.decRel H.Adj;
       letI : DecidableRel K.Adj := Classical.decRel K.Adj;
       H.edgeFinset.card <= K.edgeFinset.card) /\
      (forall L : SimpleGraph V, K <= L -> HasPlanarDrawingOn L ->
        (letI : DecidableRel L.Adj := Classical.decRel L.Adj;
         letI : DecidableRel K.Adj := Classical.decRel K.Adj;
         L.edgeFinset.card <= K.edgeFinset.card)) := by
  exact WilliamsonShmoys.finite_supergraph_card_maximal__p2m_67fa8ed9_e0b5_4d6e_a654_f64162c7a789_a1
    HasPlanarDrawingOn H hH