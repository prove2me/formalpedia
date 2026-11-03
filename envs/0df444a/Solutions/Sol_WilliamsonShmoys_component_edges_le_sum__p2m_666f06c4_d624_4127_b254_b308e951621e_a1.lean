-- Prove2me | solution 1 for WilliamsonShmoys.component_edges_le_sum__p2m_666f06c4_d624_4127_b254_b308e951621e_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T10:21:53.389769+00:00
-- url     : https://prove2.me/submissions/7c39fb53-5f19-44a8-94c7-7ecb5b2b0c43

import Mathlib
import Theorems.Thm_WilliamsonShmoys_component_induced_edge_ncard_sum

set_option maxHeartbeats 0

open Finset

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) :
    letI : Fintype K.ConnectedComponent := Fintype.ofFinite _
    letI : (L : SimpleGraph V) → DecidableRel L.Adj := fun L => Classical.decRel L.Adj
    K.edgeFinset.card ≤ ∑ c : K.ConnectedComponent,
      (letI : Fintype {v : V // v ∈ c.supp} := Fintype.ofFinite _
       letI : DecidableRel ((K.induce c.supp).Adj) := Classical.decRel _
       (K.induce c.supp).edgeFinset.card) := by
  classical
  letI : Fintype K.ConnectedComponent := Fintype.ofFinite _
  have hu :
      (@Finset.univ K.ConnectedComponent SetLike.instFintype) =
        (@Finset.univ K.ConnectedComponent (Fintype.ofFinite _)) := by
    ext c
    simp
  have h := WilliamsonShmoys.component_induced_edge_ncard_sum K
  have h' := h.symm
  rw [hu] at h'
  have hs :
      (∑ c : K.ConnectedComponent, (K.induce c.supp).edgeSet.ncard) =
        ∑ c : K.ConnectedComponent,
          (letI : Fintype {v : V // v ∈ c.supp} := Fintype.ofFinite _
           letI : DecidableRel ((K.induce c.supp).Adj) := Classical.decRel _
           (K.induce c.supp).edgeFinset.card) := by
    apply Finset.sum_congr rfl
    intro c hc
    letI : Fintype {v : V // v ∈ c.supp} := Fintype.ofFinite _
    letI : DecidableRel ((K.induce c.supp).Adj) := Classical.decRel _
    rw [← Set.fintypeCard_eq_ncard]
    exact SimpleGraph.edgeFinset_card.symm
  rw [hs] at h'
  have hK : K.edgeFinset.card = K.edgeSet.ncard := by
    rw [← Set.fintypeCard_eq_ncard]
    exact SimpleGraph.edgeFinset_card
  have heq : K.edgeFinset.card = ∑ c : K.ConnectedComponent,
      (letI : Fintype {v : V // v ∈ c.supp} := Fintype.ofFinite _
       letI : DecidableRel ((K.induce c.supp).Adj) := Classical.decRel _
       (K.induce c.supp).edgeFinset.card) := by
    calc
      K.edgeFinset.card = K.edgeSet.ncard := hK
      _ = _ := h'
  exact heq.le
