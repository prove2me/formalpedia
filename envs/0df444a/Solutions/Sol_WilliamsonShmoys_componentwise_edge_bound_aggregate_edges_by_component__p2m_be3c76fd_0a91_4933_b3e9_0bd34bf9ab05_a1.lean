-- Prove2me | solution 1 for WilliamsonShmoys.componentwise_edge_bound_aggregate_edges_by_component__p2m_be3c76fd_0a91_4933_b3e9_0bd34bf9ab05_a1
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-11T12:57:38.321215+00:00
-- url     : https://prove2.me/submissions/c956df84-7bf7-4b6b-80d1-2dbbe648f9e1

import Mathlib

open scoped BigOperators

set_option autoImplicit false

/-- Aggregating componentwise edge bounds against the component edge partition. -/
theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hcomp : ∀ c : K.ConnectedComponent, 3 ≤ c.supp.ncard →
      (K.induce c.supp).edgeSet.ncard ≤ 3 * c.supp.ncard - 6) :
    K.edgeSet.ncard ≤
      ∑ c : K.ConnectedComponent,
        if 3 ≤ c.supp.ncard then 3 * c.supp.ncard - 6 else c.supp.ncard / 2 := by
  classical
  have hedge_sum : (∑ c : K.ConnectedComponent, (K.induce c.supp).edgeSet.ncard) =
      K.edgeSet.ncard := by
    set B : K.ConnectedComponent → Finset (Sym2 V) :=
      fun c => K.edgeFinset ∩ (c.supp).toFinset.sym2 with hB
    have hterm : ∀ c : K.ConnectedComponent,
        (K.induce (c.supp : Set V)).edgeSet.ncard = (B c).card := by
      intro c
      rw [Set.ncard_eq_toFinset_card']
      change (K.induce (c.supp : Set V)).edgeFinset.card = (B c).card
      rw [← Finset.card_map (f := (Function.Embedding.subtype (· ∈ (c.supp : Set V))).sym2Map)]
      rw [SimpleGraph.map_edgeFinset_induce (s := (c.supp : Set V)) (G := K)]
    have hnonempty : ∀ e : Sym2 V, e.toFinset.Nonempty := by
      intro e
      induction e using Sym2.ind with
      | _ u v => exact ⟨u, by simp⟩
    have hmem : ∀ e ∈ K.edgeFinset, e ∈ Finset.univ.biUnion B := by
      intro e he
      revert he
      induction e using Sym2.ind with
      | _ u v =>
        intro he
        have h1 : s(u, v) ∈ K.edgeSet := by simpa [SimpleGraph.edgeFinset] using he
        have hadj : K.Adj u v := (SimpleGraph.mem_edgeSet K).mp h1
        refine Finset.mem_biUnion.mpr ⟨K.connectedComponentMk u, Finset.mem_univ _, ?_⟩
        simp only [hB, Finset.mem_inter]
        refine ⟨he, ?_⟩
        rw [Finset.mem_sym2_iff]
        intro a ha
        have hu : u ∈ (K.connectedComponentMk u).supp := rfl
        have hv : v ∈ (K.connectedComponentMk u).supp :=
          SimpleGraph.ConnectedComponent.mem_supp_of_adj_mem_supp _ hu hadj
        rw [Set.mem_toFinset]
        rcases Sym2.mem_iff.mp ha with h | h
        · rw [h]; exact hu
        · rw [h]; exact hv
    have hcover : Finset.univ.biUnion B = K.edgeFinset := by
      ext e
      refine ⟨?_, hmem e⟩
      intro he
      rw [Finset.mem_biUnion] at he
      obtain ⟨c, _, hc⟩ := he
      exact (Finset.mem_inter.mp hc).1
    have hdisj : ((Finset.univ : Finset K.ConnectedComponent) : Set K.ConnectedComponent).PairwiseDisjoint B := by
      intro c _ c' _ hne
      change Disjoint (B c) (B c')
      rw [Finset.disjoint_left]
      intro e he he'
      simp only [hB, Finset.mem_inter] at he he'
      rw [Finset.mem_sym2_iff] at he he'
      obtain ⟨a, ha⟩ := hnonempty e
      have ha' : a ∈ e := by rwa [Sym2.mem_toFinset] at ha
      have hc : a ∈ c.supp := by
        have h := he.2 a ha'
        rwa [Set.mem_toFinset] at h
      have hc' : a ∈ c'.supp := by
        have h := he'.2 a ha'
        rwa [Set.mem_toFinset] at h
      exact hne (SimpleGraph.ConnectedComponent.eq_of_common_vertex hc hc')
    have hcard : K.edgeFinset.card = ∑ c : K.ConnectedComponent, (B c).card := by
      rw [← hcover, Finset.card_biUnion hdisj]
    calc (∑ c : K.ConnectedComponent, (K.induce (c.supp : Set V)).edgeSet.ncard)
        = ∑ c, (B c).card := Finset.sum_congr rfl (fun c _ => hterm c)
      _ = K.edgeFinset.card := hcard.symm
      _ = K.edgeSet.ncard := by
          rw [Set.ncard_eq_toFinset_card']
          rfl
  rw [← hedge_sum]
  apply Finset.sum_le_sum
  intro c _
  by_cases h3 : 3 ≤ c.supp.ncard
  · rw [if_pos h3]
    exact hcomp c h3
  · rw [if_neg h3]
    have hpos : 0 < c.supp.ncard := by
      rw [Set.ncard_pos]
      exact SimpleGraph.ConnectedComponent.nonempty_supp c
    have hsmall : c.supp.ncard ≤ 2 := by omega
    have h1 : (K.induce c.supp).edgeFinset.card ≤ (Fintype.card c.supp).choose 2 :=
      SimpleGraph.card_edgeFinset_le_card_choose_two
    have h2 : (K.induce c.supp).edgeSet.ncard = (K.induce c.supp).edgeFinset.card := by
      rw [Set.ncard_eq_toFinset_card']
      rfl
    have hcard : Fintype.card c.supp = c.supp.ncard := by
      rw [Set.ncard_eq_toFinset_card', Set.toFinset_card]
    have hle : (K.induce c.supp).edgeFinset.card ≤ c.supp.ncard / 2 := by
      have hchoose : (Fintype.card c.supp).choose 2 = c.supp.ncard.choose 2 := by rw [hcard]
      rw [hchoose, Nat.choose_two_right] at h1
      have hn : c.supp.ncard = 1 ∨ c.supp.ncard = 2 := by omega
      rcases hn with hn | hn <;> rw [hn] at h1 ⊢ <;> omega
    rw [h2]
    exact hle
