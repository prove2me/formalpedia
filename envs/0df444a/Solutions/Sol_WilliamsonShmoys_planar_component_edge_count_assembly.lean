-- Prove2me | solution 1 for WilliamsonShmoys.planar_component_edge_count_assembly
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T09:42:27.225858+00:00
-- url     : https://prove2.me/submissions/420d3735-0968-4638-b4fc-8064bd34e7ae

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

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

theorem S183comp
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (P : Finset (Finset V))
    (hpartition : ∀ v : V, ∃! S : Finset V, S ∈ P ∧ v ∈ S)
    (hedgeInternal : ∀ ⦃u v : V⦄, G.Adj u v → ∃ S : Finset V, S ∈ P ∧ u ∈ S ∧ v ∈ S)
    (hlarge : ∀ S : Finset V, S ∈ P → 3 ≤ S.card →
      (G.induce (S : Set V)).edgeSet.ncard + 6 ≤ 3 * S.card)
    (hsmall : ∀ S : Finset V, S ∈ P → S.card < 3 →
      2 * (G.induce (S : Set V)).edgeSet.ncard ≤ S.card) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  classical
  set C := P.filter (fun S => S.Nonempty) with hCdef
  have hne : ∀ S ∈ C, S.Nonempty := fun S hS => (Finset.mem_filter.1 hS).2
  have hsub : ∀ S ∈ C, S ∈ P := fun S hS => (Finset.mem_filter.1 hS).1
  have huniq : ∀ v : V, ∃! S : Finset V, S ∈ C ∧ v ∈ S := by
    intro v
    obtain ⟨S, ⟨hS, hv⟩, hU⟩ := hpartition v
    exact ⟨S, ⟨Finset.mem_filter.2 ⟨hS, ⟨v, hv⟩⟩, hv⟩, fun T hT => hU T ⟨hsub T hT.1, hT.2⟩⟩
  have hcross : ∀ ⦃u v : V⦄, G.Adj u v → ∃ S ∈ C, u ∈ S ∧ v ∈ S := by
    intro u v h
    obtain ⟨S, hS, hu, hv⟩ := hedgeInternal h
    exact ⟨S, Finset.mem_filter.2 ⟨hS, ⟨u, hu⟩⟩, hu, hv⟩
  have hsum := S181agg V G C ⟨hne, huniq⟩ hcross
  have hcomp : ∀ S ∈ C, (G.induce (↑S : Set V)).edgeSet.ncard + 3 ≤ 3 * S.card := by
    intro S hS
    by_cases h3 : 3 ≤ S.card
    · have := hlarge S (hsub S hS) h3
      omega
    · have h1 : 1 ≤ S.card := Finset.card_pos.2 (hne S hS)
      have := hsmall S (hsub S hS) (by omega)
      omega
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
    obtain ⟨S, hS1⟩ := Finset.card_eq_one.1 hC1
    rw [hS1] at hsum hn
    simp only [Finset.sum_singleton] at hsum hn
    have := hlarge S (hsub S (by rw [hS1]; exact Finset.mem_singleton_self S)) (by omega)
    omega

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hcomp : ∀ (c : M.ConnectedComponent),
      [Fintype {v : V // M.connectedComponentMk v = c}] →
      let S : Type := {v : V // M.connectedComponentMk v = c}
      let H : SimpleGraph S := M.induce (fun v => M.connectedComponentMk v = c)
      3 ≤ Fintype.card S → H.edgeSet.ncard ≤ 3 * Fintype.card S - 6) :
    M.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  classical
  have key : M.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
    refine S183comp M hV (Finset.univ.image (fun c : M.ConnectedComponent => c.supp.toFinset)) ?_ ?_ ?_ ?_
    · intro v
      refine ⟨(M.connectedComponentMk v).supp.toFinset,
        ⟨Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩, by
          simp [SimpleGraph.ConnectedComponent.mem_supp_iff]⟩, ?_⟩
      rintro S ⟨hS, hv⟩
      obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hS
      simp only [Set.mem_toFinset, SimpleGraph.ConnectedComponent.mem_supp_iff] at hv
      rw [hv]
    · intro u v h
      refine ⟨(M.connectedComponentMk u).supp.toFinset,
        Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩, by
          simp [SimpleGraph.ConnectedComponent.mem_supp_iff], ?_⟩
      simp only [Set.mem_toFinset, SimpleGraph.ConnectedComponent.mem_supp_iff]
      exact (SimpleGraph.ConnectedComponent.eq.2 h.reachable).symm
    · intro S hS h3
      obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hS
      have hcard : c.supp.toFinset.card = Fintype.card {v : V // M.connectedComponentMk v = c} := by
        rw [Set.toFinset_card]; exact Fintype.card_congr (Equiv.refl _)
      have hc := hcomp c (by rw [← hcard]; exact h3)
      rw [hcard]
      have hset : ((c.supp.toFinset : Finset V) : Set V) = (fun v => M.connectedComponentMk v = c) := by
        rw [Set.coe_toFinset]; rfl
      rw [hset]
      have : 3 ≤ Fintype.card {v : V // M.connectedComponentMk v = c} := by rw [← hcard]; exact h3
      have h4 := Nat.add_le_of_le_sub (by omega) hc
      exact h4
    · intro S _ h3
      have h := S181small M S
      have h2 : 2 * S.card.choose 2 ≤ S.card := by
        interval_cases S.card <;> decide
      omega
  omega
