-- Prove2me | solution 1 for WilliamsonShmoys.connected_component_partition_decomposition__p2m_ac4d32fd_da9a_4d4d_92cd_7d05f79f270c_a1
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-11T12:41:29.374578+00:00
-- url     : https://prove2.me/submissions/7e8644a1-ae97-414c-ae16-97f6714cec2f

import Mathlib

open scoped BigOperators

set_option autoImplicit false

/-- The connected components of a finite graph give a partition of the vertex set into
nonempty connected blocks whose induced edge counts sum to the total edge count. -/
theorem solution {V : Type} [Fintype V] (H : SimpleGraph V) :
    ∃ (parts : Finset (Finset V)),
      (∑ s ∈ parts, Fintype.card {v // v ∈ s}) = Fintype.card V ∧
      (∑ s ∈ parts, (H.induce (↑s : Set V)).edgeSet.ncard) = H.edgeSet.ncard ∧
      ∀ s ∈ parts, 1 ≤ Fintype.card {v // v ∈ s} ∧
        (H.induce (↑s : Set V)).Connected := by
  classical
  let f : H.ConnectedComponent → Finset V := fun c => c.supp.toFinset
  let parts : Finset (Finset V) := Finset.univ.image f
  have hinj : ∀ c ∈ (Finset.univ : Finset H.ConnectedComponent),
      ∀ c' ∈ (Finset.univ : Finset H.ConnectedComponent), f c = f c' → c = c' := by
    intro c _ c' _ h
    apply SimpleGraph.ConnectedComponent.supp_injective
    have h' : (↑(f c) : Set V) = (↑(f c') : Set V) := by rw [h]
    dsimp only [f] at h'
    rwa [Set.coe_toFinset, Set.coe_toFinset] at h'
  refine ⟨parts, ?_, ?_, ?_⟩
  · -- vertex accounting
    have hcard : ∀ c : H.ConnectedComponent,
        Fintype.card {v // v ∈ f c} = c.supp.ncard := by
      intro c
      rw [Fintype.card_coe, Set.ncard_eq_toFinset_card']
    have hsum : (∑ c : H.ConnectedComponent, c.supp.ncard) = Fintype.card V := by
      have hpair : Pairwise fun c c' : H.ConnectedComponent => Disjoint c.supp c'.supp :=
        SimpleGraph.pairwise_disjoint_supp_connectedComponent H
      have hfin : ∀ c : H.ConnectedComponent, (c.supp).Finite := fun c => Set.toFinite _
      have h := Set.ncard_iUnion_of_finite (s := fun c : H.ConnectedComponent => c.supp) hfin hpair
      rw [SimpleGraph.iUnion_connectedComponentSupp H, Set.ncard_univ,
        Nat.card_eq_fintype_card] at h
      rw [h]
      exact (finsum_eq_sum_of_fintype
        (fun c : H.ConnectedComponent => (c.supp).ncard)).symm
    calc (∑ s ∈ parts, Fintype.card {v // v ∈ s})
        = ∑ c : H.ConnectedComponent, Fintype.card {v // v ∈ f c} := by
          dsimp only [parts]
          rw [Finset.sum_image hinj]
      _ = ∑ c : H.ConnectedComponent, c.supp.ncard := Finset.sum_congr rfl (fun c _ => hcard c)
      _ = Fintype.card V := hsum
  · -- edge accounting
    have hterm : ∀ c : H.ConnectedComponent,
        (H.induce (↑(f c) : Set V)).edgeSet.ncard = (H.induce c.supp).edgeSet.ncard := by
      intro c
      rw [show (↑(f c) : Set V) = c.supp from by dsimp only [f]; exact Set.coe_toFinset c.supp]
    have hedge : (∑ c : H.ConnectedComponent, (H.induce c.supp).edgeSet.ncard) =
        H.edgeSet.ncard := by
      set B : H.ConnectedComponent → Finset (Sym2 V) :=
        fun c => H.edgeFinset ∩ (c.supp).toFinset.sym2 with hB
      have hBterm : ∀ c : H.ConnectedComponent,
          (H.induce (c.supp : Set V)).edgeSet.ncard = (B c).card := by
        intro c
        rw [Set.ncard_eq_toFinset_card']
        change (H.induce (c.supp : Set V)).edgeFinset.card = (B c).card
        rw [← Finset.card_map (f := (Function.Embedding.subtype (· ∈ (c.supp : Set V))).sym2Map)]
        rw [SimpleGraph.map_edgeFinset_induce (s := (c.supp : Set V)) (G := H)]
      have hnonempty : ∀ e : Sym2 V, e.toFinset.Nonempty := by
        intro e
        induction e using Sym2.ind with
        | _ u v => exact ⟨u, by simp⟩
      have hmem : ∀ e ∈ H.edgeFinset, e ∈ Finset.univ.biUnion B := by
        intro e he
        revert he
        induction e using Sym2.ind with
        | _ u v =>
          intro he
          have h1 : s(u, v) ∈ H.edgeSet := by simpa [SimpleGraph.edgeFinset] using he
          have hadj : H.Adj u v := (SimpleGraph.mem_edgeSet H).mp h1
          refine Finset.mem_biUnion.mpr ⟨H.connectedComponentMk u, Finset.mem_univ _, ?_⟩
          simp only [hB, Finset.mem_inter]
          refine ⟨he, ?_⟩
          rw [Finset.mem_sym2_iff]
          intro a ha
          have hu : u ∈ (H.connectedComponentMk u).supp := rfl
          have hv : v ∈ (H.connectedComponentMk u).supp :=
            SimpleGraph.ConnectedComponent.mem_supp_of_adj_mem_supp _ hu hadj
          rw [Set.mem_toFinset]
          rcases Sym2.mem_iff.mp ha with h | h
          · rw [h]; exact hu
          · rw [h]; exact hv
      have hcover : Finset.univ.biUnion B = H.edgeFinset := by
        ext e
        refine ⟨?_, hmem e⟩
        intro he
        rw [Finset.mem_biUnion] at he
        obtain ⟨c, _, hc⟩ := he
        exact (Finset.mem_inter.mp hc).1
      have hdisj : ((Finset.univ : Finset H.ConnectedComponent) : Set H.ConnectedComponent).PairwiseDisjoint B := by
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
      have hcard : H.edgeFinset.card = ∑ c : H.ConnectedComponent, (B c).card := by
        rw [← hcover, Finset.card_biUnion hdisj]
      calc (∑ c : H.ConnectedComponent, (H.induce (c.supp : Set V)).edgeSet.ncard)
          = ∑ c, (B c).card := Finset.sum_congr rfl (fun c _ => hBterm c)
        _ = H.edgeFinset.card := hcard.symm
        _ = H.edgeSet.ncard := by
            rw [Set.ncard_eq_toFinset_card']
            rfl
    calc (∑ s ∈ parts, (H.induce (↑s : Set V)).edgeSet.ncard)
        = ∑ c : H.ConnectedComponent, (H.induce (↑(f c) : Set V)).edgeSet.ncard := by
          dsimp only [parts]
          rw [Finset.sum_image hinj]
      _ = ∑ c : H.ConnectedComponent, (H.induce c.supp).edgeSet.ncard :=
          Finset.sum_congr rfl (fun c _ => hterm c)
      _ = H.edgeSet.ncard := hedge
  · -- each block is nonempty and connected
    intro s hs
    rw [Finset.mem_image] at hs
    obtain ⟨c, -, rfl⟩ := hs
    constructor
    · rw [Fintype.card_coe]
      obtain ⟨v, hv⟩ := SimpleGraph.ConnectedComponent.nonempty_supp c
      have hv' : v ∈ f c := by
        dsimp only [f]
        rwa [Set.mem_toFinset]
      have hpos : 0 < (f c).card := Finset.card_pos.mpr ⟨v, hv'⟩
      omega
    · rw [show (↑(f c) : Set V) = c.supp from by dsimp only [f]; exact Set.coe_toFinset c.supp]
      exact c.connected_toSimpleGraph
