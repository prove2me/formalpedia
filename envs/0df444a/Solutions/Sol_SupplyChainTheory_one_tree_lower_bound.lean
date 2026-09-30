-- Prove2me | solution 1 for SupplyChainTheory.one_tree_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-25T20:42:33.580687+00:00
-- url     : https://prove2.me/submissions/f5425e72-dcfe-410b-a7b1-efae219645e1

import Mathlib
import Definitions.Def_SupplyChainTheory_tsp

open Classical SupplyChainTheory

/-! ### Counting tour edges by position (on `Fin (m + 1)`, so that `k + 1` makes sense) -/

/-- The successor position on a tour. -/
private lemma rot_eq {m : ℕ} (k : Fin (m + 1)) : finRotate (m + 1) k = k + 1 := finRotate_apply k

/-- For at least three nodes, distinct positions give distinct tour edges. -/
private lemma tourEdge_injective {m : ℕ} (hm : 2 ≤ m) (τ : Equiv.Perm (Fin (m + 1))) :
    Function.Injective (fun k : Fin (m + 1) => s(τ k, τ (finRotate (m + 1) k))) := by
  intro a b h
  simp only [Sym2.eq_iff] at h
  rcases h with ⟨h1, _⟩ | ⟨h1, h2⟩
  · exact τ.injective h1
  · have e1 := τ.injective h1
    have e2 := τ.injective h2
    rw [rot_eq] at e1 e2
    -- `a = b + 1` and `a + 1 = b` force `1 + 1 = 0` in `Fin (m + 1)`, impossible for `m ≥ 2`.
    exfalso
    have h3 : b + (1 + 1) = b + 0 := by rw [add_zero, ← add_assoc, ← e1, e2]
    have h4 : ((1 + 1 : Fin (m + 1)) : ℕ) = 0 := by
      rw [add_left_cancel h3]; rfl
    rw [Fin.val_add, Fin.val_one', Nat.one_mod_eq_one.mpr (by omega),
      Nat.mod_eq_of_lt (by omega)] at h4
    omega

/-- Counting tour edges with a property is counting positions with that property. -/
private lemma card_tourEdges_filter {m : ℕ} (hm : 2 ≤ m) (τ : Equiv.Perm (Fin (m + 1)))
    (P : Sym2 (Fin (m + 1)) → Prop) [DecidablePred P] :
    ((tourEdges τ).filter P).card
      = (Finset.univ.filter (fun k => P s(τ k, τ (finRotate (m + 1) k)))).card := by
  rw [tourEdges, Finset.filter_image, Finset.card_image_of_injective _ (tourEdge_injective hm τ)]

private lemma edgesWithin_eq {m : ℕ} (hm : 2 ≤ m) (τ : Equiv.Perm (Fin (m + 1)))
    (S : Finset (Fin (m + 1))) :
    edgesWithin τ S
      = (Finset.univ.filter (fun k => τ k ∈ S ∧ τ (finRotate (m + 1) k) ∈ S)).card := by
  rw [edgesWithin, card_tourEdges_filter hm]
  congr 1; ext k; simp

private lemma edgesLeaving_eq {m : ℕ} (hm : 2 ≤ m) (τ : Equiv.Perm (Fin (m + 1)))
    (S : Finset (Fin (m + 1))) :
    edgesLeaving τ S
      = (Finset.univ.filter (fun k => (τ k ∈ S ↔ τ (finRotate (m + 1) k) ∉ S))).card := by
  rw [edgesLeaving, card_tourEdges_filter hm]
  congr 1; ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Sym2.mem_iff]
  constructor
  · rintro ⟨v, hv, hvS, w, hw, hwS⟩
    rcases hv with rfl | rfl <;> rcases hw with rfl | rfl <;> tauto
  · intro h
    by_cases ha : τ k ∈ S
    · exact ⟨τ k, Or.inl rfl, ha, τ (finRotate (m + 1) k), Or.inr rfl, h.mp ha⟩
    · have hb : τ (finRotate (m + 1) k) ∈ S := by by_contra hb; exact ha (h.mpr hb)
      exact ⟨τ (finRotate (m + 1) k), Or.inr rfl, hb, τ k, Or.inl rfl, ha⟩

/-- Degree equation of a tour: every node has tour degree `2`, so
`2 x(E(S)) + x(δ(S)) = 2|S|`. -/
private lemma degree_identity {m : ℕ} (hm : 2 ≤ m) (τ : Equiv.Perm (Fin (m + 1)))
    (S : Finset (Fin (m + 1))) : 2 * edgesWithin τ S + edgesLeaving τ S = 2 * S.card := by
  rw [edgesWithin_eq hm, edgesLeaving_eq hm]
  simp only [Finset.card_filter]
  have hperm : ∀ σ : Equiv.Perm (Fin (m + 1)), ∑ k, (if σ k ∈ S then 1 else 0) = S.card := by
    intro σ
    rw [Equiv.sum_comp σ (fun v => if v ∈ S then 1 else 0), ← Finset.card_filter]
    congr 1; ext v; simp
  have hA := hperm τ
  have hB : ∑ k, (if τ (finRotate (m + 1) k) ∈ S then 1 else 0) = S.card :=
    hperm (τ * finRotate (m + 1))
  calc 2 * (∑ k, if τ k ∈ S ∧ τ (finRotate (m + 1) k) ∈ S then 1 else 0)
        + ∑ k, (if (τ k ∈ S ↔ τ (finRotate (m + 1) k) ∉ S) then 1 else 0)
      = ∑ k, ((if τ k ∈ S then 1 else 0) + if τ (finRotate (m + 1) k) ∈ S then 1 else 0) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        split_ifs <;> simp_all
    _ = 2 * S.card := by rw [Finset.sum_add_distrib, hA, hB]; ring

/-- A tour leaves every nonempty proper node set. -/
private lemma exists_leaving {m : ℕ} (τ : Equiv.Perm (Fin (m + 1))) (S : Finset (Fin (m + 1)))
    (hS : S.Nonempty) (hS' : S ≠ Finset.univ) :
    ∃ k, τ k ∈ S ∧ τ (finRotate (m + 1) k) ∉ S := by
  by_contra hno
  push Not at hno
  obtain ⟨v, hv⟩ := hS
  -- Walking along the tour from `v` never leaves `S`, so `S` contains every node.
  have hall : ∀ j : ℕ, τ ((finRotate (m + 1) ^ j) (τ.symm v)) ∈ S := by
    intro j
    induction j with
    | zero => simpa using hv
    | succ j ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact hno _ ih
  apply hS'
  ext w
  simp only [Finset.mem_univ, iff_true]
  rcases Nat.eq_zero_or_pos m with hm0 | hm0
  · subst hm0
    have hwv : w = v := Fin.ext (by have := w.isLt; have := v.isLt; omega)
    rw [hwv]; exact hv
  -- `finRotate` is a single cycle through every position.
  have hsupp : ∀ k : Fin (m + 1), finRotate (m + 1) k ≠ k := by
    intro k
    rw [← Equiv.Perm.mem_support, support_finRotate_of_le (by omega)]
    exact Finset.mem_univ k
  obtain ⟨j, hj⟩ := (isCycle_finRotate_of_le (by omega)).exists_pow_eq
    (hsupp (τ.symm v)) (hsupp (τ.symm w))
  have := hall j
  rw [hj] at this
  simpa using this

/-- Subtour elimination: a tour has at most `|S| - 1` edges inside a nonempty proper set. -/
private lemma subtour {m : ℕ} (hm : 2 ≤ m) (τ : Equiv.Perm (Fin (m + 1)))
    (S : Finset (Fin (m + 1))) (hS : S.Nonempty) (hS' : S ≠ Finset.univ) :
    edgesWithin τ S + 1 ≤ S.card := by
  have hid := degree_identity hm τ S
  have hl : 1 ≤ edgesLeaving τ S := by
    obtain ⟨k, hk1, hk2⟩ := exists_leaving τ S hS hS'
    rw [edgesLeaving_eq hm]
    exact Finset.card_pos.mpr ⟨k, by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact iff_of_true hk1 hk2⟩
  omega
/-! ### A tour as a graph, and as a 1-tree -/

/-- The cycle graph of a tour: its edges are the tour edges. -/
private def cycG {n : ℕ} (τ : Equiv.Perm (Fin n)) : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet (tourEdges τ : Set (Sym2 (Fin n)))

private lemma tourEdge_not_diag {m : ℕ} (hm : 2 ≤ m) (τ : Equiv.Perm (Fin (m + 1)))
    (e : Sym2 (Fin (m + 1))) (he : e ∈ tourEdges τ) : ¬ e.IsDiag := by
  simp only [tourEdges, Finset.mem_image, Finset.mem_univ, true_and] at he
  obtain ⟨k, rfl⟩ := he
  rw [Sym2.mk_isDiag_iff, rot_eq]
  intro h
  have h1 := τ.injective h
  have h2 : (1 : Fin (m + 1)) = 0 := by
    have := congrArg (· - k) h1; simpa using this.symm
  have := congrArg Fin.val h2
  rw [Fin.val_one', Nat.one_mod_eq_one.mpr (by omega)] at this
  simp at this

private lemma cycG_edgeFinset {m : ℕ} (hm : 2 ≤ m) (τ : Equiv.Perm (Fin (m + 1)))
    [Fintype (cycG τ).edgeSet] : (cycG τ).edgeFinset = tourEdges τ := by
  ext e
  rw [SimpleGraph.mem_edgeFinset, cycG, SimpleGraph.edgeSet_fromEdgeSet]
  exact ⟨fun h => h.1, fun h => ⟨h, tourEdge_not_diag hm τ e h⟩⟩

/-- Under symmetric distances, the cycle graph of a tour weighs the tour length. -/
private lemma cycG_weight {m : ℕ} (hm : 2 ≤ m) (c : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hsymm : ∀ i j, c i j = c j i) (τ : Equiv.Perm (Fin (m + 1))) :
    graphWeight c (cycG τ) = tourLength c τ := by
  rw [graphWeight, cycG_edgeFinset hm, tourEdges,
    Finset.sum_image (fun a _ b _ h => tourEdge_injective hm τ h), tourLength]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp only [edgeCost, Sym2.lift_mk]
  rw [hsymm (τ (finRotate (m + 1) k))]; ring

/-- Rotating the starting position does not change the tour length. -/
private lemma tourLength_rotate {m : ℕ} (c : Fin (m + 1) → Fin (m + 1) → ℝ)
    (τ : Equiv.Perm (Fin (m + 1))) (j : Fin (m + 1)) :
    tourLength c (τ * Equiv.addRight j) = tourLength c τ := by
  simp only [tourLength, Equiv.Perm.coe_mul, Function.comp_apply, Equiv.coe_addRight, rot_eq]
  have := Equiv.sum_comp (Equiv.addRight j) (fun k => c (τ k) (τ (k + 1)))
  simp only [Equiv.coe_addRight] at this
  rw [← this]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [add_right_comm]

/-- The cycle graph of a tour starting at `r` is a 1-tree rooted at `r`. -/
private lemma cycG_is1Tree {m : ℕ} (hm : 2 ≤ m) (τ : Equiv.Perm (Fin (m + 1))) :
    Is1Tree (τ 0) (cycG τ) := by
  have hadj : ∀ u v, (cycG τ).Adj u v ↔ s(u, v) ∈ tourEdges τ ∧ u ≠ v := by
    intro u v; simp [cycG]
  have hmemT : ∀ k : Fin (m + 1), s(τ k, τ (k + 1)) ∈ tourEdges τ := by
    intro k
    simp only [tourEdges, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨k, by rw [rot_eq]⟩
  -- Positions `1, …, m` are exactly the positions whose node differs from `τ 0`.
  have hne0 : ∀ k : Fin (m + 1), τ k ≠ τ 0 ↔ k ≠ 0 := fun k => τ.injective.ne_iff
  have hmem : ∀ (j : ℕ) (hj1 : 1 ≤ j) (hj : j < m + 1), τ ⟨j, hj⟩ ∈ {v | v ≠ τ 0} :=
    fun j hj1 hj => (hne0 _).mpr (fun h => by have := congrArg Fin.val h; simp at this; omega)
  constructor
  · rw [SimpleGraph.isTree_iff_connected_and_card]
    constructor
    · -- Connected: walk along positions `1, 2, …, m`.
      have hreach : ∀ (j : ℕ) (hj1 : 1 ≤ j) (hj : j < m + 1),
          ((cycG τ).induce {v | v ≠ τ 0}).Reachable
            ⟨τ ⟨1, by omega⟩, hmem 1 le_rfl (by omega)⟩ ⟨τ ⟨j, hj⟩, hmem j hj1 hj⟩ := by
        intro j hj1
        induction j with
        | zero => omega
        | succ j ih =>
          intro hj
          rcases Nat.eq_zero_or_pos j with rfl | hjpos
          · rfl
          refine (ih hjpos (by omega)).trans (SimpleGraph.Adj.reachable ?_)
          rw [SimpleGraph.induce_adj, hadj]
          refine ⟨?_, fun h => ?_⟩
          · have := hmemT ⟨j, by omega⟩
            convert this using 3
            ext
            rw [Fin.val_add_one_of_lt (by rw [Fin.lt_def]; simp; omega)]
          · have := congrArg Fin.val (τ.injective h); simp at this
      have : Nonempty {v : Fin (m + 1) | v ≠ τ 0} := ⟨⟨_, hmem 1 le_rfl (by omega)⟩⟩
      refine SimpleGraph.Connected.mk (fun u v => ?_)
      have key : ∀ w : {v : Fin (m + 1) | v ≠ τ 0},
          ((cycG τ).induce {v | v ≠ τ 0}).Reachable
            ⟨τ ⟨1, by omega⟩, hmem 1 le_rfl (by omega)⟩ w := by
        rintro ⟨w, hw⟩
        have hk : (τ.symm w).val ≠ 0 := by
          intro h0; apply hw; rw [← Equiv.apply_symm_apply τ w]; congr 1; exact Fin.ext h0
        have := hreach (τ.symm w).val (by omega) (τ.symm w).isLt
        simpa using this
      exact (key u).symm.trans (key v)
    · -- Edge count: the `m - 1` tour edges avoiding `τ 0`, on `m` nodes.
      classical
      have hV : Nat.card {v : Fin (m + 1) | v ≠ τ 0} = m := by
        rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card']
        simp [Finset.filter_ne']
      have hE : ((cycG τ).induce {v | v ≠ τ 0}).edgeFinset.card
          = ((tourEdges τ).filter (fun e => τ 0 ∉ e)).card := by
        refine Finset.card_bij (fun e _ => Sym2.map Subtype.val e) ?_ ?_ ?_
        · intro e he
          induction e using Sym2.ind with
          | h a b =>
            rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, SimpleGraph.induce_adj,
              hadj] at he
            simp only [Sym2.map_mk, Finset.mem_filter, Sym2.mem_iff, not_or]
            exact ⟨he.1, fun h => a.2 h.symm, fun h => b.2 h.symm⟩
        · intro a _ b _ h
          exact Sym2.map.injective Subtype.val_injective h
        · intro e he
          induction e using Sym2.ind with
          | h u v =>
            simp only [Finset.mem_filter, Sym2.mem_iff, not_or] at he
            obtain ⟨he, hu, hv⟩ := he
            refine ⟨s(⟨u, Ne.symm hu⟩, ⟨v, Ne.symm hv⟩), ?_, by simp⟩
            rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, SimpleGraph.induce_adj,
              hadj]
            refine ⟨he, fun huv => ?_⟩
            have huv' : u = v := huv
            exact tourEdge_not_diag hm τ _ he (Sym2.mk_isDiag_iff.mpr huv')
      have hcount : ((tourEdges τ).filter (fun e => τ 0 ∉ e)).card = m - 1 := by
        have hpos0 : ∀ k, τ 0 = τ k ↔ k = 0 := fun k => ⟨fun h => (τ.injective h).symm, fun h => by rw [h]⟩
        have hposl : ∀ k, τ 0 = τ (finRotate (m + 1) k) ↔ k = Fin.last m := by
          intro k
          constructor
          · intro h
            have := τ.injective h
            rw [← finRotate_last] at this
            exact ((finRotate _).injective this).symm
          · intro h; rw [h, finRotate_last]
        rw [card_tourEdges_filter hm]
        have : Finset.univ.filter (fun k => τ 0 ∉ s(τ k, τ (finRotate (m + 1) k)))
            = Finset.univ \ {0, Fin.last m} := by
          ext k
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Sym2.mem_iff, not_or,
            Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
          rw [hpos0, hposl]
        rw [this, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
          Fintype.card_fin, Finset.card_pair (by simp [Fin.ext_iff]; omega : (0 : Fin (m + 1)) ≠ Fin.last m)]
        omega
      rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card, hE, hcount, hV]
      omega
  · -- The root `τ 0` lies on exactly the two tour edges at positions `0` and `m`.
    classical
    rw [← SimpleGraph.card_incidenceFinset_eq_degree]
    have : (cycG τ).incidenceFinset (τ 0) = (tourEdges τ).filter (fun e => τ 0 ∈ e) := by
      ext e
      rw [SimpleGraph.mem_incidenceFinset, SimpleGraph.incidenceSet, Finset.mem_filter,
        ← cycG_edgeFinset hm τ, SimpleGraph.mem_edgeFinset]
      rfl
    rw [this, card_tourEdges_filter hm]
    have hpos0 : ∀ k, τ 0 = τ k ↔ k = 0 := fun k => ⟨fun h => (τ.injective h).symm, fun h => by rw [h]⟩
    have hposl : ∀ k, τ 0 = τ (finRotate (m + 1) k) ↔ k = Fin.last m := by
      intro k
      constructor
      · intro h
        have := τ.injective h
        rw [← finRotate_last] at this
        exact ((finRotate _).injective this).symm
      · intro h; rw [h, finRotate_last]
    have : Finset.univ.filter (fun k => τ 0 ∈ s(τ k, τ (finRotate (m + 1) k)))
        = {0, Fin.last m} := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Sym2.mem_iff,
        Finset.mem_insert, Finset.mem_singleton]
      rw [hpos0, hposl]
    rw [this, Finset.card_pair (by simp [Fin.ext_iff]; omega : (0 : Fin (m + 1)) ≠ Fin.last m)]

/-- `z*` is the length of some tour. -/
private lemma exists_opt_tour {n : ℕ} (c : Fin n → Fin n → ℝ) :
    ∃ τ : Equiv.Perm (Fin n), tourLength c τ = optTourLength c := by
  obtain ⟨τ, hτ⟩ := (Set.range_nonempty (tourLength c)).csInf_mem (Set.finite_range _)
  exact ⟨τ, hτ⟩

/-- Some optimal tour starts at any prescribed node `r`. -/
private lemma exists_opt_tour_from {m : ℕ} (c : Fin (m + 1) → Fin (m + 1) → ℝ) (r : Fin (m + 1)) :
    ∃ τ : Equiv.Perm (Fin (m + 1)), τ 0 = r ∧ tourLength c τ = optTourLength c := by
  obtain ⟨τ, hτ⟩ := exists_opt_tour c
  refine ⟨τ * Equiv.addRight (τ.symm r), by simp, ?_⟩
  rw [tourLength_rotate, hτ]

theorem solution {n : ℕ} (c : Fin n → Fin n → ℝ) (hc : IsMetric c) (hn : 3 ≤ n)
    (r : Fin n) : opt1TreeLength c r ≤ optTourLength c := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm : 2 ≤ m := by omega
  -- An optimal tour through `r`, read as a graph, is a 1-tree rooted at `r`.
  obtain ⟨τ, hτr, hτ⟩ := exists_opt_tour_from c r
  have h1 : Is1Tree r (cycG τ) := hτr ▸ cycG_is1Tree hm τ
  -- Tree lengths are nonnegative, so the infimum is well defined.
  have hbdd : BddBelow {w | ∃ G : SimpleGraph (Fin (m + 1)), Is1Tree r G ∧ w = graphWeight c G} := by
    refine ⟨0, ?_⟩
    rintro w ⟨G, _, rfl⟩
    refine Finset.sum_nonneg (fun e _ => ?_)
    induction e using Sym2.ind with
    | h i j =>
      simp only [edgeCost, Sym2.lift_mk]
      linarith [hc.nonneg i j, hc.nonneg j i]
  calc opt1TreeLength c r ≤ graphWeight c (cycG τ) := csInf_le hbdd ⟨_, h1, rfl⟩
    _ = tourLength c τ := cycG_weight hm c hc.symm τ
    _ = optTourLength c := hτ
