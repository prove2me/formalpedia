-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_2629fd8d_6fc9_4c07_8b09_9c33cf4a1063_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T07:30:12.349216+00:00
-- url     : https://prove2.me/submissions/32b7c39e-037f-4784-b08d-874cc9c31e53

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count__p2m_de26d9eb_6d23_47e8_ab7e_7d74d86b498f_a1

open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : HasPlanarDrawingOn H)
    (hcard : 3 <= Fintype.card V)
    (hmax : forall K : SimpleGraph V,
      (forall u v, H.Adj u v -> K.Adj u v) -> HasPlanarDrawingOn K ->
      forall u v, K.Adj u v -> H.Adj u v) :
    3 * Fintype.card V <= H.edgeFinset.card + 6 := by
  classical
  have hmax' : forall K : SimpleGraph V, H <= K -> HasPlanarDrawingOn K -> K <= H := by
    intro K hHK hK u v huv
    exact hmax K (fun a b hab => hHK hab) hK u v huv
  have hcount : H.edgeSet.ncard = H.edgeFinset.card := by
    simpa only [Set.fintypeCard_eq_ncard] using
      (SimpleGraph.card_edgeSet (G := H))
  have heq : 3 * Fintype.card V = H.edgeSet.ncard + 6 :=
    WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_de26d9eb_6d23_47e8_ab7e_7d74d86b498f_a1
      H hH hcard hmax'
  have hfinal : 3 * Fintype.card V = H.edgeFinset.card + 6 := by
    calc
      3 * Fintype.card V = H.edgeSet.ncard + 6 := heq
      _ = H.edgeFinset.card + 6 := by rw [hcount]
  exact le_of_eq hfinal