-- Prove2me | solution 1 for OPG37271.exists_one_regular_of_bridgeless_cubic
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T06:16:20.5375+00:00
-- url     : https://prove2.me/submissions/bcce3b33-24b8-4170-a12a-51df9e4917cb

import Definitions.Def_opg37271_star_edge_coloring
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Tutte

set_option autoImplicit false

open OPG37271

universe u

private lemma card_filter_adj_eq_three
    {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcubic : ∀ v : V, (G.neighborSet v).encard = 3) (v : V) :
    (Finset.univ.filter (fun w => G.Adj v w)).card = 3 := by
  have hset : ((Finset.univ.filter (fun w => G.Adj v w) : Finset V) : Set V) = G.neighborSet v := by
    ext w
    simp [SimpleGraph.mem_neighborSet]
  have hencard : (((Finset.univ.filter (fun w => G.Adj v w)).card : ℕ) : ℕ∞) = (3 : ℕ) := by
    rw [← Set.encard_coe_eq_coe_finsetCard, hset]
    exact hcubic v
  exact Nat.cast_injective hencard

private lemma card_ordered_edges_from
    {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcubic : ∀ v : V, (G.neighborSet v).encard = 3) (A : Finset V) :
    ((A ×ˢ (Finset.univ : Finset V)).filter (fun p => G.Adj p.1 p.2)).card = 3 * A.card := by
  have hbij :
      ((A ×ˢ (Finset.univ : Finset V)).filter (fun p => G.Adj p.1 p.2)).card =
        (A.sigma (fun x => Finset.univ.filter (fun y => G.Adj x y))).card := by
    refine Finset.card_bij (fun p _ => ⟨p.1, p.2⟩) ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true, true_and,
        Finset.mem_sigma] at hp ⊢
      exact hp
    · intro p₁ _ p₂ _ heq
      cases p₁
      cases p₂
      simpa using heq
    · intro a ha
      simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and] at ha
      refine ⟨(a.1, a.2), ?_, ?_⟩
      · simp [ha.1, ha.2]
      · cases a
        rfl
  rw [hbij, Finset.card_sigma]
  simp_rw [card_filter_adj_eq_three G hcubic, Finset.sum_const, smul_eq_mul, mul_comm]

private lemma card_ordered_edges_to
    {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcubic : ∀ v : V, (G.neighborSet v).encard = 3) (U : Finset V) :
    (((Finset.univ : Finset V) ×ˢ U).filter (fun p => G.Adj p.1 p.2)).card = 3 * U.card := by
  have hbij :
      (((Finset.univ : Finset V) ×ˢ U).filter (fun p => G.Adj p.1 p.2)).card =
        (U.sigma (fun y => Finset.univ.filter (fun x => G.Adj y x))).card := by
    refine Finset.card_bij (fun p _ => ⟨p.2, p.1⟩) ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and,
        Finset.mem_sigma] at hp ⊢
      exact ⟨hp.1, hp.2.symm⟩
    · intro p₁ _ p₂ _ heq
      rcases p₁ with ⟨x₁, y₁⟩
      rcases p₂ with ⟨x₂, y₂⟩
      simp only [ Sigma.mk.inj_iff, heq_eq_eq] at heq
      exact Prod.ext heq.2 heq.1
    · intro a ha
      simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and] at ha
      refine ⟨(a.2, a.1), ?_, ?_⟩
      · simp [ha.1, ha.2.symm]
      · cases a
        rfl
  rw [hbij, Finset.card_sigma]
  simp_rw [card_filter_adj_eq_three G hcubic, Finset.sum_const, smul_eq_mul, mul_comm]

private lemma even_card_ordered_internal_edges
    {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) :
    Even ((A ×ˢ A).filter (fun p => G.Adj p.1 p.2)).card := by
  let H : SimpleGraph {x : V // x ∈ A} := G.induce {x : V | x ∈ A}
  have h2 := H.two_mul_card_edgeFinset
  have hbij :
      (Finset.univ.filter (fun (x, y) => H.Adj x y)).card =
        ((A ×ˢ A).filter (fun p => G.Adj p.1 p.2)).card := by
    refine Finset.card_bij (fun xy _ => (xy.1.1, xy.2.1)) ?_ ?_ ?_
    · rintro ⟨x, y⟩ hxy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product] at hxy ⊢
      exact ⟨⟨x.2, y.2⟩, hxy⟩
    · intro xy₁ _ xy₂ _ heq
      rcases xy₁ with ⟨⟨x₁, hx₁⟩, ⟨y₁, hy₁⟩⟩
      rcases xy₂ with ⟨⟨x₂, hx₂⟩, ⟨y₂, hy₂⟩⟩
      simp only [Prod.mk.injEq] at heq
      ext <;> simp [heq.1, heq.2]
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_product] at hp
      refine ⟨(⟨p.1, hp.1.1⟩, ⟨p.2, hp.1.2⟩), ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hp.2
      · cases p
        rfl
  refine ⟨H.edgeFinset.card, ?_⟩
  rw [← hbij, ← h2]
  ring

private lemma walk_mem_of_closed
    {V : Type u} {G' : SimpleGraph V} {A : Finset V}
    (hclosed : ∀ x ∈ A, ∀ y : V, G'.Adj x y → y ∈ A) :
    ∀ {a b : V}, G'.Walk a b → a ∈ A → b ∈ A
  | _, _, .nil, ha => ha
  | _, _, .cons hadj p, ha => walk_mem_of_closed hclosed p (hclosed _ ha _ hadj)

private lemma not_isTutteViolator_of_bridgeless_cubic
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    (hcubic : ∀ v : V, (G.neighborSet v).encard = 3)
    (hbridgeless : ∀ u v : V, G.Adj u v → (G.deleteEdges {s(u, v)}).Reachable u v)
    (u : Set V) :
    ¬ G.IsTutteViolator u := by
  classical
  let H : G.Subgraph := (⊤ : G.Subgraph).deleteVerts u
  let U : Finset V := u.toFinset
  let O : Finset H.coe.ConnectedComponent := H.coe.oddComponents.toFinset
  let S : H.coe.ConnectedComponent → Finset V := fun c =>
    Finset.univ.filter (fun v => ∃ hv : v ∈ H.verts, ⟨v, hv⟩ ∈ c.supp)
  let B : H.coe.ConnectedComponent → Finset (V × V) := fun c =>
    (S c ×ˢ U).filter (fun p => G.Adj p.1 p.2)
  have hS_disj_U : ∀ c : H.coe.ConnectedComponent, Disjoint (S c) U := by
    intro c
    rw [Finset.disjoint_left]
    intro v hvS hvU
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, H,
      SimpleGraph.Subgraph.deleteVerts_verts, SimpleGraph.Subgraph.verts_top,
      Set.mem_sdiff, Set.mem_univ] at hvS
    rcases hvS with ⟨hv_not_u, _⟩
    simp only [U, Set.mem_toFinset] at hvU
    exact hv_not_u hvU
  have hS_closed : ∀ (c : H.coe.ConnectedComponent) {v w : V},
      v ∈ S c → G.Adj v w → w ∈ S c ∨ w ∈ U := by
    intro c v w hvS hadj
    by_cases hwu : w ∈ u
    · right
      simpa [U] using hwu
    · left
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hvS ⊢
      rcases hvS with ⟨hvH, hvc⟩
      have hwH : w ∈ H.verts := by
        simp [H, hwu]
      refine ⟨hwH, c.mem_supp_of_adj_mem_supp hvc ?_⟩
      simp only [SimpleGraph.Subgraph.coe_adj, H, SimpleGraph.Subgraph.deleteVerts_adj,
        SimpleGraph.Subgraph.verts_top, Set.mem_univ, SimpleGraph.Subgraph.top_adj, true_and]
      have hv_not_u : v ∉ u := by
        simpa [H] using hvH
      exact ⟨hv_not_u, hwu, hadj⟩
  have hS_card : ∀ c : H.coe.ConnectedComponent, (S c).card = c.supp.ncard := by
    intro c
    have hcoe : ((S c : Finset V) : Set V) = Subtype.val '' c.supp := by
      ext v
      simp only [Finset.mem_coe, S, Finset.mem_filter, Finset.mem_univ, true_and,
        Set.mem_image, Subtype.exists]
      exact ⟨fun ⟨hv, hvc⟩ => ⟨v, hv, hvc, rfl⟩, fun ⟨_, hv, hvc, heq⟩ => heq ▸ ⟨hv, hvc⟩⟩
    rw [← Set.ncard_coe_finset, hcoe, Set.ncard_image_of_injective _ Subtype.val_injective]
  have hS_pairwise : (O : Set H.coe.ConnectedComponent).PairwiseDisjoint S := by
    intro c₁ _ c₂ _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro v hv₁ hv₂
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hv₁ hv₂
    rcases hv₁ with ⟨hvH₁, hvc₁⟩
    rcases hv₂ with ⟨_, hvc₂⟩
    exact hne (SimpleGraph.ConnectedComponent.eq_of_common_vertex hvc₁ hvc₂)
  have hB_ge_three : ∀ c ∈ O, 3 ≤ (B c).card := by
    intro c hcO
    have hc_odd : Odd (S c).card := by
      rw [hS_card]
      simpa [O, SimpleGraph.oddComponents] using hcO
    let I : Finset (V × V) := (S c ×ˢ S c).filter (fun p => G.Adj p.1 p.2)
    let E : Finset (V × V) := (S c ×ˢ (Finset.univ : Finset V)).filter (fun p => G.Adj p.1 p.2)
    have hE_eq : E = I ∪ B c := by
      ext ⟨x, y⟩
      simp only [E, I, B, Finset.mem_union, Finset.mem_filter, Finset.mem_product,
        Finset.mem_univ, and_true]
      constructor
      · rintro ⟨hx, hadj⟩
        rcases hS_closed c hx hadj with hyS | hyU
        · exact Or.inl ⟨⟨hx, hyS⟩, hadj⟩
        · exact Or.inr ⟨⟨hx, hyU⟩, hadj⟩
      · rintro (⟨⟨hx, _⟩, hadj⟩ | ⟨⟨hx, _⟩, hadj⟩) <;> exact ⟨hx, hadj⟩
    have hIB_disj : Disjoint I (B c) := by
      rw [Finset.disjoint_left]
      intro p hpI hpB
      simp only [I, B, Finset.mem_filter, Finset.mem_product] at hpI hpB
      exact Finset.disjoint_left.mp (hS_disj_U c) hpI.1.2 hpB.1.2
    have hE_card : E.card = 3 * (S c).card := card_ordered_edges_from G hcubic (S c)
    have hE_split : E.card = I.card + (B c).card := by
      rw [hE_eq, Finset.card_union_of_disjoint hIB_disj]
    have hI_even : Even I.card := even_card_ordered_internal_edges G (S c)
    have hB_ne_one : (B c).card ≠ 1 := by
      intro hcard1
      rcases Finset.card_eq_one.mp hcard1 with ⟨⟨x₀, y₀⟩, hBeq⟩
      have hmem₀ : (x₀, y₀) ∈ B c := by simp [hBeq]
      simp only [B, Finset.mem_filter, Finset.mem_product] at hmem₀
      rcases hmem₀ with ⟨⟨hx₀S, hy₀U⟩, hadj₀⟩
      have hreach := hbridgeless x₀ y₀ hadj₀
      rcases hreach with ⟨w⟩
      have hclosed' : ∀ x ∈ S c, ∀ y : V, (G.deleteEdges {s(x₀, y₀)}).Adj x y → y ∈ S c := by
        intro x hxS y hadj'
        rw [SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff] at hadj'
        rcases hS_closed c hxS hadj'.1 with hyS | hyU
        · exact hyS
        · exfalso
          have hxyB : (x, y) ∈ B c := by
            simp [B, hxS, hyU, hadj'.1]
          rw [hBeq, Finset.mem_singleton, Prod.mk.injEq] at hxyB
          exact hadj'.2 (by rw [hxyB.1, hxyB.2])
      have hy₀S : y₀ ∈ S c := walk_mem_of_closed hclosed' w hx₀S
      exact Finset.disjoint_left.mp (hS_disj_U c) hy₀S hy₀U
    rcases hc_odd with ⟨m, hm⟩
    rcases hI_even with ⟨k, hk⟩
    omega
  have hB_pairwise : (O : Set H.coe.ConnectedComponent).PairwiseDisjoint B := by
    intro c₁ hc₁ c₂ hc₂ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro p hp₁ hp₂
    simp only [B, Finset.mem_filter, Finset.mem_product] at hp₁ hp₂
    exact Finset.disjoint_left.mp (hS_pairwise hc₁ hc₂ hne) hp₁.1.1 hp₂.1.1
  have hsum_ge : 3 * O.card ≤ ∑ c ∈ O, (B c).card := by
    calc
      3 * O.card = ∑ _c ∈ O, 3 := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ c ∈ O, (B c).card := Finset.sum_le_sum hB_ge_three
  have hsum_le : ∑ c ∈ O, (B c).card ≤ 3 * U.card := by
    rw [← Finset.card_biUnion hB_pairwise, ← card_ordered_edges_to G hcubic U]
    refine Finset.card_le_card ?_
    intro p hp
    simp only [Finset.mem_biUnion, B, Finset.mem_filter, Finset.mem_product,
      Finset.mem_univ, true_and] at hp ⊢
    rcases hp with ⟨_, _, ⟨_, hpU⟩, hadj⟩
    exact ⟨hpU, hadj⟩
  have hcard_le : O.card ≤ U.card := by omega
  simp only [SimpleGraph.IsTutteViolator, not_lt]
  have hu_ncard : u.ncard = U.card := Set.ncard_eq_toFinset_card' u
  have ho_ncard : H.coe.oddComponents.ncard = O.card :=
    Set.ncard_eq_toFinset_card' H.coe.oddComponents
  change H.coe.oddComponents.ncard ≤ u.ncard
  omega

/-- **Petersen's Theorem (1891)** (`Subgraph.IsPerfectMatching` form):
Every finite bridgeless cubic simple graph admits a perfect matching. -/
private theorem exists_isPerfectMatching_of_bridgeless_cubic
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    (hcubic : ∀ v : V, (G.neighborSet v).encard = 3)
    (hbridgeless : ∀ u v : V, G.Adj u v → (G.deleteEdges {s(u, v)}).Reachable u v) :
    ∃ M : G.Subgraph, M.IsPerfectMatching :=
  SimpleGraph.tutte.mpr (not_isTutteViolator_of_bridgeless_cubic G hcubic hbridgeless)

/-- **Petersen's Theorem (1891)** (1-regular spanning subgraph form):
Every finite bridgeless cubic simple graph contains a 1-regular spanning subgraph. -/
theorem solution
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    (hcubic : ∀ v : V, (G.neighborSet v).encard = 3)
    (hbridgeless : ∀ u v : V, G.Adj u v → (G.deleteEdges {s(u, v)}).Reachable u v) :
    ∃ M : SimpleGraph V, M ≤ G ∧ ∀ v : V, (M.neighborSet v).encard = 1 := by
  obtain ⟨M, hM⟩ := exists_isPerfectMatching_of_bridgeless_cubic G hcubic hbridgeless
  refine ⟨M.spanningCoe, M.spanningCoe_le, fun v => ?_⟩
  obtain ⟨w, hvw, huniq⟩ := SimpleGraph.Subgraph.isPerfectMatching_iff.mp hM v
  have hset : M.spanningCoe.neighborSet v = {w} := by
    ext x
    simp only [SimpleGraph.mem_neighborSet, SimpleGraph.Subgraph.spanningCoe_adj,
      Set.mem_singleton_iff]
    exact ⟨fun hx => huniq x hx, fun h => h ▸ hvw⟩
  rw [hset, Set.encard_singleton]

