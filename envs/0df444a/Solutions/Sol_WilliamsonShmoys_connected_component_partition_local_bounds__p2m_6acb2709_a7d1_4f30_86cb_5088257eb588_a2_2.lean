-- Prove2me | solution 2 for WilliamsonShmoys.connected_component_partition_local_bounds__p2m_6acb2709_a7d1_4f30_86cb_5088257eb588_a2
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-11T13:02:27.990484+00:00
-- url     : https://prove2.me/submissions/23abbdb9-f21f-4453-886f-62a43ae832b4

import Mathlib

open scoped BigOperators

set_option autoImplicit false

/-- A connected vertex set that is either small or large satisfies the local edge allowance. -/
private lemma local_bound_cond {V : Type} [Fintype V] (H : SimpleGraph V)
    (hBound : ∀ (s : Finset V), (H.induce (↑s : Set V)).Connected →
      3 ≤ Fintype.card {v // v ∈ s} →
      (H.induce (↑s : Set V)).edgeSet.ncard + 6 ≤ 3 * Fintype.card {v // v ∈ s})
    (s : Finset V) (hNonempty : 1 ≤ Fintype.card {v // v ∈ s})
    (hConnected : (H.induce (↑s : Set V)).Connected) :
    (H.induce (↑s : Set V)).edgeSet.ncard +
        (if 3 ≤ Fintype.card {v // v ∈ s} then 6 else 3) ≤
      3 * Fintype.card {v // v ∈ s} := by
  classical
  by_cases h3 : 3 ≤ Fintype.card {v // v ∈ s}
  · rw [if_pos h3]
    exact hBound s hConnected h3
  · rw [if_neg h3]
    have hcard : Fintype.card {v // v ∈ s} = s.card := Fintype.card_coe s
    have hm1 : 1 ≤ s.card := by rw [← hcard]; exact hNonempty
    have hm2 : s.card ≤ 2 := by rw [← hcard]; omega
    have h2 : (H.induce (↑s : Set V)).edgeSet.ncard =
        (H.induce (↑s : Set V)).edgeFinset.card := by
      rw [Set.ncard_eq_toFinset_card']
      rfl
    have h1 : (H.induce (↑s : Set V)).edgeFinset.card ≤ s.card.choose 2 := by
      have := SimpleGraph.card_edgeFinset_le_card_choose_two (G := H.induce (↑s : Set V))
      simpa [hcard] using this
    rw [h2, hcard]
    have hm : s.card = 1 ∨ s.card = 2 := by omega
    rcases hm with hm | hm
    · rw [hm] at h1 ⊢
      norm_num at h1 ⊢
      omega
    · rw [hm] at h1 ⊢
      norm_num at h1 ⊢
      omega

/-- The connected components of a finite graph form a partition into nonempty connected blocks
that each satisfy the local edge allowance, and their vertex/edge counts add up. -/
theorem solution {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hBound : ∀ (s : Finset V), (H.induce (↑s : Set V)).Connected →
      3 ≤ Fintype.card {v // v ∈ s} →
      (H.induce (↑s : Set V)).edgeSet.ncard + 6 ≤ 3 * Fintype.card {v // v ∈ s}) :
    ∃ (parts : Finset (Finset V)),
      (∑ s ∈ parts, Fintype.card {v // v ∈ s}) = Fintype.card V ∧
      (∑ s ∈ parts, (H.induce (↑s : Set V)).edgeSet.ncard) = H.edgeSet.ncard ∧
      ∀ s ∈ parts, 1 ≤ Fintype.card {v // v ∈ s} ∧
        (H.induce (↑s : Set V)).Connected ∧
        (H.induce (↑s : Set V)).edgeSet.ncard +
          (if 3 ≤ Fintype.card {v // v ∈ s} then 6 else 3) ≤
        3 * Fintype.card {v // v ∈ s} := by
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
  · -- each block is nonempty, connected, and locally bounded
    intro s hs
    rw [Finset.mem_image] at hs
    obtain ⟨c, -, rfl⟩ := hs
    have hnonempty : 1 ≤ Fintype.card {v // v ∈ f c} := by
      rw [Fintype.card_coe]
      obtain ⟨v, hv⟩ := SimpleGraph.ConnectedComponent.nonempty_supp c
      have hv' : v ∈ f c := by
        dsimp only [f]
        rwa [Set.mem_toFinset]
      have hpos : 0 < (f c).card := Finset.card_pos.mpr ⟨v, hv'⟩
      omega
    have hconn : (H.induce (↑(f c) : Set V)).Connected := by
      rw [show (↑(f c) : Set V) = c.supp from by dsimp only [f]; exact Set.coe_toFinset c.supp]
      exact c.connected_toSimpleGraph
    exact ⟨hnonempty, hconn, local_bound_cond H hBound (f c) hnonempty hconn⟩
