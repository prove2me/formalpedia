-- Prove2me | solution 1 for WilliamsonShmoys.component_vertex_accounting_edge_sum__p2m_d7ae0e86_02e7_434a_acfe_3fef1dc883ec_a1
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-10T16:27:47.958246+00:00
-- url     : https://prove2.me/submissions/f0d46d35-e0e6-4372-9c0a-536a9ae18ad9

import Mathlib

open scoped BigOperators

/-- The edge sets of the induced subgraphs on the connected components of a finite graph
partition its edge set. -/
theorem solution {V : Type*} [Fintype V] [LinearOrder V] (L : SimpleGraph V)
    [Fintype L.ConnectedComponent] :
    (Finset.univ.sum fun c : L.ConnectedComponent =>
      (L.induce (SimpleGraph.ConnectedComponent.supp c)).edgeSet.ncard) = L.edgeSet.ncard := by
  classical
  set B : L.ConnectedComponent → Finset (Sym2 V) :=
    fun c => L.edgeFinset ∩ (c.supp).toFinset.sym2 with hB
  have hterm : ∀ c : L.ConnectedComponent,
      (L.induce (c.supp : Set V)).edgeSet.ncard = (B c).card := by
    intro c
    rw [Set.ncard_eq_toFinset_card']
    change (L.induce (c.supp : Set V)).edgeFinset.card = (B c).card
    rw [← Finset.card_map (f := (Function.Embedding.subtype (· ∈ (c.supp : Set V))).sym2Map)]
    rw [SimpleGraph.map_edgeFinset_induce (s := (c.supp : Set V)) (G := L)]
  have hnonempty : ∀ e : Sym2 V, e.toFinset.Nonempty := by
    intro e
    induction e using Sym2.ind with
    | _ u v => exact ⟨u, by simp⟩
  have hmem : ∀ e ∈ L.edgeFinset, e ∈ Finset.univ.biUnion B := by
    intro e he
    revert he
    induction e using Sym2.ind with
    | _ u v =>
      intro he
      have h1 : s(u, v) ∈ L.edgeSet := by simpa [SimpleGraph.edgeFinset] using he
      have hadj : L.Adj u v := (SimpleGraph.mem_edgeSet L).mp h1
      refine Finset.mem_biUnion.mpr ⟨L.connectedComponentMk u, Finset.mem_univ _, ?_⟩
      simp only [hB, Finset.mem_inter]
      refine ⟨he, ?_⟩
      rw [Finset.mem_sym2_iff]
      intro a ha
      have hu : u ∈ (L.connectedComponentMk u).supp := rfl
      have hv : v ∈ (L.connectedComponentMk u).supp :=
        SimpleGraph.ConnectedComponent.mem_supp_of_adj_mem_supp _ hu hadj
      rw [Set.mem_toFinset]
      rcases Sym2.mem_iff.mp ha with h | h
      · rw [h]; exact hu
      · rw [h]; exact hv
  have hcover : Finset.univ.biUnion B = L.edgeFinset := by
    ext e
    refine ⟨?_, hmem e⟩
    intro he
    rw [Finset.mem_biUnion] at he
    obtain ⟨c, _, hc⟩ := he
    exact (Finset.mem_inter.mp hc).1
  have hdisj : ((Finset.univ : Finset L.ConnectedComponent) : Set L.ConnectedComponent).PairwiseDisjoint B := by
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
  have hcard : L.edgeFinset.card = ∑ c : L.ConnectedComponent, (B c).card := by
    rw [← hcover, Finset.card_biUnion hdisj]
  calc (∑ c : L.ConnectedComponent, (L.induce (c.supp : Set V)).edgeSet.ncard)
      = ∑ c, (B c).card := Finset.sum_congr rfl (fun c _ => hterm c)
    _ = L.edgeFinset.card := hcard.symm
    _ = L.edgeSet.ncard := by
        rw [Set.ncard_eq_toFinset_card']
        rfl
