-- Prove2me | solution 1 for WilliamsonShmoys.component_edge_bound_aggregation__p2m_ca990ca2_90e1_475e_969d_4e2c10201187_a3
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-11T13:23:12.606756+00:00
-- url     : https://prove2.me/submissions/025be36c-b3c2-447a-ac5d-2fa433b223da

import Mathlib

open scoped BigOperators

set_option autoImplicit false

/-- Combinatorial core: positive sizes with total `n ≥ 3` give the component allowance bound. -/
private lemma comb_bound {C : Type*} [Fintype C] (m : C → Nat) (hm : ∀ c, 0 < m c)
    {n : Nat} (hn : 3 ≤ n) (hsum : (∑ c, m c) = n) :
    (∑ c, if 3 ≤ m c then 3 * m c - 6 else m c * (m c - 1) / 2) ≤ 3 * n - 6 := by
  have hkpos : 0 < Fintype.card C := by
    rcases Nat.eq_zero_or_pos (Fintype.card C) with hk0 | hkpos
    · exfalso
      haveI : IsEmpty C := Fintype.card_eq_zero_iff.mp hk0
      have h0 : (∑ c, m c) = 0 := by simp
      omega
    · exact hkpos
  rcases Nat.lt_or_ge (Fintype.card C) 2 with hlt | hge
  · have hcard1 : Fintype.card C = 1 := by omega
    obtain ⟨c, hc⟩ := Fintype.card_eq_one_iff.mp hcard1
    have hsumc : (∑ x, m x) = m c := by
      apply Finset.sum_eq_single c
      · intro b _ hb
        exact absurd (hc b) hb
      · intro h
        exact absurd (Finset.mem_univ c) h
    have hmc : m c = n := by rw [← hsumc]; exact hsum
    have hbig : 3 ≤ m c := by omega
    have hgoal : (∑ x, if 3 ≤ m x then 3 * m x - 6 else m x * (m x - 1) / 2) =
        (if 3 ≤ m c then 3 * m c - 6 else m c * (m c - 1) / 2) := by
      apply Finset.sum_eq_single c
      · intro b _ hb
        exact absurd (hc b) hb
      · intro h
        exact absurd (Finset.mem_univ c) h
    rw [hgoal, if_pos hbig, hmc]
  · have hterm : ∀ c, (if 3 ≤ m c then 3 * m c - 6 else m c * (m c - 1) / 2) ≤ 3 * m c - 3 := by
      intro c
      have hpos : 0 < m c := hm c
      rcases le_or_gt 3 (m c) with h3 | h3
      · rw [if_pos h3]
        omega
      · rw [if_neg (not_le.mpr h3)]
        have h1 : m c = 1 ∨ m c = 2 := by omega
        rcases h1 with h1 | h1 <;> simp [h1]
    have hsum_le : (∑ c, (if 3 ≤ m c then 3 * m c - 6 else m c * (m c - 1) / 2)) ≤
        ∑ c, (3 * m c - 3) :=
      Finset.sum_le_sum (fun c _ => hterm c)
    have hdistr : (∑ c, (3 * m c - 3)) = 3 * n - 3 * Fintype.card C := by
      rw [Finset.sum_tsub_distrib]
      · rw [← Finset.mul_sum, Finset.sum_const, Finset.card_univ, hsum]
        rw [Nat.nsmul_eq_mul]
        omega
      · intro c _
        have hpos : 0 < m c := hm c
        omega
    have hcard : 6 ≤ 3 * Fintype.card C := by omega
    have hfin : 3 * n - 3 * Fintype.card C ≤ 3 * n - 6 :=
      Nat.sub_le_sub_left hcard (3 * n)
    omega

/-- Any induced subgraph on a vertex set of size `m` has at most `m * (m-1) / 2` edges. -/
private lemma small_edge_bound {V : Type} [Fintype V] (H : SimpleGraph V) (s : Finset V) :
    (H.induce (↑s : Set V)).edgeSet.ncard ≤ s.card * (s.card - 1) / 2 := by
  classical
  have h1 : (H.induce (↑s : Set V)).edgeFinset.card ≤ (Fintype.card ↥(↑s : Set V)).choose 2 :=
    SimpleGraph.card_edgeFinset_le_card_choose_two
  have h2 : (H.induce (↑s : Set V)).edgeSet.ncard =
      (H.induce (↑s : Set V)).edgeFinset.card := by
    rw [Set.ncard_eq_toFinset_card']
    rfl
  rw [h2]
  calc (H.induce (↑s : Set V)).edgeFinset.card
      ≤ (Fintype.card ↥(↑s : Set V)).choose 2 := h1
    _ = s.card.choose 2 := by
        congr 1
        exact Fintype.card_coe s
    _ = s.card * (s.card - 1) / 2 := Nat.choose_two_right s.card

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hLocal : ∀ (s : Finset V), 3 ≤ s.card →
      (H.induce (s : Set V)).Connected →
      (H.induce (s : Set V)).edgeSet.ncard + 6 ≤
        3 * Fintype.card {v // v ∈ (s : Set V)}) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  classical
  have hBound : ∀ (s : Finset V),
      (H.induce (↑s : Set V)).Connected →
      3 ≤ Fintype.card {v // v ∈ s} →
      (H.induce (↑s : Set V)).edgeSet.ncard + 6 ≤ 3 * Fintype.card {v // v ∈ s} := by
    intro s hconn h3
    have h3' : 3 ≤ s.card := by rwa [Fintype.card_coe] at h3
    have h := hLocal s h3' hconn
    simpa using h
  have hcomp : ∀ c : H.ConnectedComponent,
      (H.induce c.supp).edgeSet.ncard ≤
        if 3 ≤ Fintype.card c.supp then 3 * Fintype.card c.supp - 6
        else Fintype.card c.supp * (Fintype.card c.supp - 1) / 2 := by
    intro c
    by_cases h3 : 3 ≤ Fintype.card c.supp
    · rw [if_pos h3]
      have hcard : Fintype.card {v // v ∈ c.supp.toFinset} = Fintype.card c.supp := by
        rw [Fintype.card_coe, Set.toFinset_card]
      have h := hBound c.supp.toFinset ?hconn ?hcard3
      · rw [Set.coe_toFinset, hcard] at h
        omega
      · rw [Set.coe_toFinset]
        exact c.connected_toSimpleGraph
      · rw [hcard]
        exact h3
    · rw [if_neg h3]
      have hsmall := small_edge_bound H c.supp.toFinset
      rw [Set.coe_toFinset, Set.toFinset_card] at hsmall
      exact hsmall
  have hedge_sum : (∑ c : H.ConnectedComponent, (H.induce c.supp).edgeSet.ncard) =
      H.edgeSet.ncard := by
    set B : H.ConnectedComponent → Finset (Sym2 V) :=
      fun c => H.edgeFinset ∩ (c.supp).toFinset.sym2 with hB
    have hterm : ∀ c : H.ConnectedComponent,
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
        = ∑ c, (B c).card := Finset.sum_congr rfl (fun c _ => hterm c)
      _ = H.edgeFinset.card := hcard.symm
      _ = H.edgeSet.ncard := by
          rw [Set.ncard_eq_toFinset_card']
          rfl
  have hcard_sum : (∑ c : H.ConnectedComponent, Fintype.card c.supp) = Fintype.card V := by
    have hpair : Pairwise fun c c' : H.ConnectedComponent => Disjoint c.supp c'.supp :=
      SimpleGraph.pairwise_disjoint_supp_connectedComponent H
    have hfin : ∀ c : H.ConnectedComponent, (c.supp).Finite := fun c => Set.toFinite _
    have hncard := Set.ncard_iUnion_of_finite (s := fun c : H.ConnectedComponent => c.supp) hfin hpair
    rw [SimpleGraph.iUnion_connectedComponentSupp H, Set.ncard_univ,
      Nat.card_eq_fintype_card] at hncard
    have h2 : (∑ c : H.ConnectedComponent, (c.supp).ncard) = Fintype.card V := by
      rw [hncard]
      exact (finsum_eq_sum_of_fintype (fun c : H.ConnectedComponent => (c.supp).ncard)).symm
    rw [← h2]
    apply Finset.sum_congr rfl
    intro c _
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_card]
  have hbound : H.edgeSet.ncard ≤
      ∑ c : H.ConnectedComponent,
        if 3 ≤ Fintype.card c.supp then 3 * Fintype.card c.supp - 6
        else Fintype.card c.supp * (Fintype.card c.supp - 1) / 2 := by
    calc H.edgeSet.ncard
        = (∑ c : H.ConnectedComponent, (H.induce c.supp).edgeSet.ncard) := hedge_sum.symm
      _ ≤ _ := Finset.sum_le_sum (fun c _ => hcomp c)
  have hmain := comb_bound (fun c : H.ConnectedComponent => Fintype.card c.supp)
    (fun c => by
      haveI : Nonempty c.supp := c.connected_toSimpleGraph.nonempty
      exact Fintype.card_pos) hCard hcard_sum
  omega
