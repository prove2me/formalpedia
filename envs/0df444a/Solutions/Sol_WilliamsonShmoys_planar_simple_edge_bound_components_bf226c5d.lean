-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_edge_bound_components_bf226c5d
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T06:48:15.524601+00:00
-- url     : https://prove2.me/submissions/bcd1e466-9217-4966-9fdd-3c5e722d7ba4

import Mathlib

theorem S181agg (V : Type) [Fintype V]
    (H : SimpleGraph V)
    (C : Finset (Finset V))
    (hPartition : (∀ S ∈ C, S.Nonempty) ∧
      ∀ v : V, ∃! S : Finset V, S ∈ C ∧ v ∈ S)
    (hNoCross : ∀ ⦃u v : V⦄, H.Adj u v →
      ∃ S ∈ C, u ∈ S ∧ v ∈ S) :
    H.edgeSet.ncard =
      C.sum (fun S => (H.induce (↑S : Set V)).edgeSet.ncard) := by
  classical
  let A : Finset V → Finset (Sym2 V) := fun S =>
    (H.induce (↑S : Set V)).edgeFinset.image (Sym2.map Subtype.val)
  have hA : ∀ S, (A S).card = (H.induce (↑S : Set V)).edgeSet.ncard := by
    intro S
    rw [Finset.card_image_of_injective _ (Sym2.map.injective Subtype.val_injective),
      ← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset]
  have hmem : ∀ S (e : Sym2 V), e ∈ A S →
      e ∈ H.edgeSet ∧ ∀ x ∈ e, x ∈ S := by
    intro S e he
    obtain ⟨e', he', rfl⟩ := Finset.mem_image.1 he
    rw [SimpleGraph.mem_edgeFinset] at he'
    induction e' using Sym2.ind with
    | h x y =>
      refine ⟨by simpa using he', fun z hz => ?_⟩
      rw [Sym2.map_mk, Sym2.mem_iff] at hz
      rcases hz with rfl | rfl
      · exact x.2
      · exact y.2
  have hunion : H.edgeFinset = C.biUnion A := by
    ext e
    induction e using Sym2.ind with
    | h a b =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, Finset.mem_biUnion]
      constructor
      · intro h
        obtain ⟨S, hS, ha, hb⟩ := hNoCross h
        refine ⟨S, hS, Finset.mem_image.2 ⟨s(⟨a, ha⟩, ⟨b, hb⟩), ?_, by simp⟩⟩
        rw [SimpleGraph.mem_edgeFinset]
        simpa using h
      · rintro ⟨S, -, he⟩
        exact (hmem S _ he).1
  have hE : H.edgeSet = ((C.biUnion A : Finset (Sym2 V)) : Set (Sym2 V)) := by
    rw [← hunion, SimpleGraph.coe_edgeFinset]
  rw [hE, Set.ncard_coe_finset, Finset.card_biUnion]
  · exact Finset.sum_congr rfl (fun S _ => hA S)
  · intro S hS T hT hST
    rw [Function.onFun, Finset.disjoint_left]
    intro e heS heT
    obtain ⟨e', -, rfl⟩ := Finset.mem_image.1 heS
    induction e' using Sym2.ind with
    | h x y =>
      have h1 := (hmem S _ heS).2 x.1 (by simp)
      have h2 := (hmem T _ heT).2 x.1 (by simp)
      obtain ⟨R, -, hR⟩ := hPartition.2 x.1
      exact hST ((hR S ⟨hS, h1⟩).trans (hR T ⟨hT, h2⟩).symm)
theorem S181part {V : Type} [Fintype V] (H : SimpleGraph V) :
    ∃ C : Finset (Finset V),
      (∀ S ∈ C, S.Nonempty) ∧
      (∀ v : V, ∃! S : Finset V, S ∈ C ∧ v ∈ S) ∧
      (∀ ⦃u v : V⦄, H.Adj u v → ∃ S ∈ C, u ∈ S ∧ v ∈ S) ∧
      (∀ S ∈ C, (H.induce (↑S : Set V)).Connected) := by
  classical
  refine ⟨Finset.univ.image (fun c : H.ConnectedComponent => c.supp.toFinset), ?_, ?_, ?_, ?_⟩
  · intro S hS
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hS
    induction c using SimpleGraph.ConnectedComponent.ind with
    | h v => exact ⟨v, by simp [SimpleGraph.ConnectedComponent.mem_supp_iff]⟩
  · intro v
    refine ⟨(H.connectedComponentMk v).supp.toFinset,
      ⟨Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩, by
        simp [SimpleGraph.ConnectedComponent.mem_supp_iff]⟩, ?_⟩
    rintro S ⟨hS, hv⟩
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hS
    simp only [Set.mem_toFinset, SimpleGraph.ConnectedComponent.mem_supp_iff] at hv
    rw [hv]
  · intro u v h
    refine ⟨(H.connectedComponentMk u).supp.toFinset,
      Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩, by
        simp [SimpleGraph.ConnectedComponent.mem_supp_iff], ?_⟩
    simp only [Set.mem_toFinset, SimpleGraph.ConnectedComponent.mem_supp_iff]
    exact (SimpleGraph.ConnectedComponent.eq.2 h.reachable).symm
  · intro S hS
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hS
    rw [Set.coe_toFinset]
    exact c.connected_toSimpleGraph

theorem S181small {V : Type} [Fintype V] (H : SimpleGraph V) (S : Finset V) :
    (H.induce (↑S : Set V)).edgeSet.ncard ≤ S.card.choose 2 := by
  classical
  have h := SimpleGraph.card_edgeFinset_le_card_choose_two (G := H.induce (↑S : Set V))
  rw [← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset] at h
  simpa using h

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hConnectedBounds : ∀ (S : Set V) [Fintype S],
      3 ≤ Fintype.card S →
      (G.induce S).Connected →
      (G.induce S).edgeSet.ncard + 6 ≤ 3 * Fintype.card S) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  classical
  obtain ⟨C, hne, huniq, hcross, hconn⟩ := S181part G
  have hsum := S181agg V G C ⟨hne, huniq⟩ hcross
  have hcard : ∀ S : Finset V, Fintype.card (↑S : Set V) = S.card := fun S => by simp
  -- per-component bound
  have hcomp : ∀ S ∈ C, (G.induce (↑S : Set V)).edgeSet.ncard + 3 ≤ 3 * S.card := by
    intro S hS
    by_cases h3 : 3 ≤ S.card
    · have := hConnectedBounds (↑S : Set V) (by rw [hcard]; exact h3) (hconn S hS)
      rw [hcard] at this
      omega
    · have h1 : 1 ≤ S.card := Finset.card_pos.2 (hne S hS)
      have hs := S181small G S
      have hc1 : Nat.choose 1 2 = 0 := rfl
      have hc2 : Nat.choose 2 2 = 1 := rfl
      rcases (by omega : S.card = 1 ∨ S.card = 2) with h | h
      · rw [h, hc1] at hs; omega
      · rw [h, hc2] at hs; omega
  -- sizes sum to card V
  have hdisj : (C : Set (Finset V)).PairwiseDisjoint id := by
    intro S hS T hT hST
    rw [Function.onFun, id, id, Finset.disjoint_left]
    intro v hvS hvT
    obtain ⟨R, -, hR⟩ := huniq v
    exact hST ((hR S ⟨hS, hvS⟩).trans (hR T ⟨hT, hvT⟩).symm)
  have hcov : C.biUnion id = Finset.univ := by
    ext v
    simp only [Finset.mem_biUnion, id, Finset.mem_univ, iff_true]
    obtain ⟨S, ⟨hS, hv⟩, -⟩ := huniq v
    exact ⟨S, hS, hv⟩
  have hn : C.sum (fun S => S.card) = Fintype.card V := by
    have := Finset.card_biUnion hdisj
    rw [hcov, Finset.card_univ] at this
    simpa using this.symm
  rcases Nat.lt_or_ge 1 C.card with hC | hC
  · have h2 : C.sum (fun S => (G.induce (↑S : Set V)).edgeSet.ncard + 3) ≤
        C.sum (fun S => 3 * S.card) := Finset.sum_le_sum hcomp
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hn, Finset.sum_const, smul_eq_mul] at h2
    omega
  · have hC1 : C.card = 1 := by
      have : C.Nonempty := by
        have hV' : Nonempty V := Fintype.card_pos_iff.mp (by omega)
        obtain ⟨S, ⟨hS, -⟩, -⟩ := huniq (Classical.arbitrary V)
        exact ⟨S, hS⟩
      have := Finset.card_pos.2 this
      omega
    obtain ⟨S, rfl⟩ := Finset.card_eq_one.1 hC1
    simp only [Finset.sum_singleton] at hsum hn
    have := hConnectedBounds (↑S : Set V) (by rw [hcard]; omega) (hconn S (Finset.mem_singleton_self S))
    rw [hcard] at this
    omega
