-- Prove2me | solution 1 for WeldedPath.forest_coefficient_stability
-- status  : ACCEPTED   (prove)
-- author  : @dmilosch
-- created : 2026-11-17T23:11:36.156715+00:00
-- url     : https://prove2.me/submissions/5e3e77ac-3d9d-4c56-9e7c-85454af27a60

import Definitions.Def_WeldedPath_Supplement_projGood
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Prod.Lex
import Mathlib.Tactic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Prod
import Definitions.Def_WeldedPath_Supplement_pCross
import Definitions.Def_WeldedPath_bEdge
import Definitions.Def_WeldedPath_InjDb
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Algebra.Order.Chebyshev
import Definitions.Def_WeldedPath_Nb
import Definitions.Def_WeldedPath_Supplement_pWt
import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp

set_option autoImplicit false

-- Solutions.WeldedPathFixedData
section

namespace WeldedPath.Supplement.FixedData

variable {n : ℕ}

lemma reachable_closed {V : Type*} {J : SimpleGraph V} (P : V → Prop)
    (hstep : ∀ u v, P u → J.Adj u v → P v) {u v : V} (h : J.Reachable u v) :
    P u → P v := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact id
  | cons huv w ih => exact fun hu => ih (hstep _ _ hu huv)

/-- Agreement of incident edges on a component suffices to preserve that
entire component; arbitrary edges wholly outside it are irrelevant. -/
lemma reachable_iff_of_adj_at_component {V : Type*} (J K : SimpleGraph V) (s : V)
    (hadj : ∀ u v, J.Reachable s u → (J.Adj u v ↔ K.Adj u v)) (v : V) :
    J.Reachable s v ↔ K.Reachable s v := by
  constructor
  · intro hv
    have h := reachable_closed (fun u => J.Reachable s u ∧ K.Reachable s u)
      (fun u v hu huv => ⟨hu.1.trans huv.reachable,
        hu.2.trans ((hadj u v hu.1).mp huv).reachable⟩) hv
        ⟨SimpleGraph.Reachable.refl _, SimpleGraph.Reachable.refl _⟩
    exact h.2
  · intro hv
    exact reachable_closed (fun u => J.Reachable s u)
      (fun u v hu huv => hu.trans ((hadj u v hu).mpr huv).reachable) hv
      (SimpleGraph.Reachable.refl _)

lemma ctree_subset_sfix (H : AbsForest n) (φ : Fin H.k → Label n) (s : Fin H.k) :
    H.Ctree φ s ⊆ H.Sfix φ s := by
  classical
  exact Finset.subset_union_left

/-- Every stored edge touching the selected tree component has both its
endpoints in the recorded fixed set. -/
lemma edge_endpoints_mem_sfix (H : AbsForest n) (hH : H.IsValid)
    (φ : Fin H.k → Label n) (s : Fin H.k) (p : Fin H.k × Fin H.k) (hp : p ∈ H.E)
    (htouch : p.1 ∈ H.Ctree φ s ∨ p.2 ∈ H.Ctree φ s) :
    p.1 ∈ H.Sfix φ s ∧ p.2 ∈ H.Sfix φ s := by
  classical
  by_cases hw : H.IsWeldUnder φ p
  · rcases htouch with h₁ | h₂
    · refine ⟨ctree_subset_sfix H φ s h₁, ?_⟩
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, p, hp, hw, Or.inl ⟨h₁, rfl⟩⟩)
    · refine ⟨?_, ctree_subset_sfix H φ s h₂⟩
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, p, hp, hw, Or.inr ⟨h₂, rfl⟩⟩)
  · have hr : (H.treeGraph φ).Reachable p.1 p.2 :=
      SimpleGraph.Adj.reachable ⟨ne_of_lt (hH.1 p hp), Or.inl ⟨hp, hw⟩⟩
    rcases htouch with h₁ | h₂
    · have h₂ : p.2 ∈ H.Ctree φ s := by
        simp only [AbsForest.Ctree, Finset.mem_filter, Finset.mem_univ, true_and] at h₁ ⊢
        exact h₁.trans hr
      exact ⟨ctree_subset_sfix H φ s h₁, ctree_subset_sfix H φ s h₂⟩
    · have h₁ : p.1 ∈ H.Ctree φ s := by
        simp only [AbsForest.Ctree, Finset.mem_filter, Finset.mem_univ, true_and] at h₂ ⊢
        exact h₂.trans hr.symm
      exact ⟨ctree_subset_sfix H φ s h₁, ctree_subset_sfix H φ s h₂⟩

lemma weld_iff_of_agree_sfix (H : AbsForest n) (hH : H.IsValid)
    (φ φ₀ : Fin H.k → Label n) (s : Fin H.k)
    (hφ : ∀ u ∈ H.Sfix φ₀ s, φ u = φ₀ u)
    (p : Fin H.k × Fin H.k) (hp : p ∈ H.E)
    (htouch : p.1 ∈ H.Ctree φ₀ s ∨ p.2 ∈ H.Ctree φ₀ s) :
    H.IsWeldUnder φ p ↔ H.IsWeldUnder φ₀ p := by
  obtain ⟨h₁, h₂⟩ := edge_endpoints_mem_sfix H hH φ₀ s p hp htouch
  simp only [AbsForest.IsWeldUnder, hφ p.1 h₁, hφ p.2 h₂]

lemma treeGraph_adj_iff_of_agree_sfix (H : AbsForest n) (hH : H.IsValid)
    (φ φ₀ : Fin H.k → Label n) (s : Fin H.k)
    (hφ : ∀ u ∈ H.Sfix φ₀ s, φ u = φ₀ u)
    (u v : Fin H.k) (hu : u ∈ H.Ctree φ₀ s) :
    (H.treeGraph φ).Adj u v ↔ (H.treeGraph φ₀).Adj u v := by
  have h₁ (hp : (u, v) ∈ H.E) :=
    weld_iff_of_agree_sfix H hH φ φ₀ s hφ (u, v) hp (Or.inl hu)
  have h₂ (hp : (v, u) ∈ H.E) :=
    weld_iff_of_agree_sfix H hH φ φ₀ s hφ (v, u) hp (Or.inr hu)
  constructor
  · rintro ⟨hne, ⟨hp, hn⟩ | ⟨hp, hn⟩⟩
    · exact ⟨hne, Or.inl ⟨hp, (not_congr (h₁ hp)).mp hn⟩⟩
    · exact ⟨hne, Or.inr ⟨hp, (not_congr (h₂ hp)).mp hn⟩⟩
  · rintro ⟨hne, ⟨hp, hn⟩ | ⟨hp, hn⟩⟩
    · exact ⟨hne, Or.inl ⟨hp, (not_congr (h₁ hp)).mpr hn⟩⟩
    · exact ⟨hne, Or.inr ⟨hp, (not_congr (h₂ hp)).mpr hn⟩⟩

lemma ctree_eq_of_agree_sfix (H : AbsForest n) (hH : H.IsValid)
    (φ φ₀ : Fin H.k → Label n) (s : Fin H.k)
    (hφ : ∀ u ∈ H.Sfix φ₀ s, φ u = φ₀ u) : H.Ctree φ s = H.Ctree φ₀ s := by
  classical
  apply Finset.ext
  intro v
  simp only [AbsForest.Ctree, Finset.mem_filter, Finset.mem_univ, true_and]
  apply (reachable_iff_of_adj_at_component (H.treeGraph φ₀) (H.treeGraph φ) s ?_ v).symm
  intro u v hu
  apply (treeGraph_adj_iff_of_agree_sfix H hH φ φ₀ s hφ u v ?_).symm
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩

lemma sfix_eq_of_agree_sfix (H : AbsForest n) (hH : H.IsValid)
    (φ φ₀ : Fin H.k → Label n) (s : Fin H.k)
    (hφ : ∀ u ∈ H.Sfix φ₀ s, φ u = φ₀ u) : H.Sfix φ s = H.Sfix φ₀ s := by
  classical
  have hC := ctree_eq_of_agree_sfix H hH φ φ₀ s hφ
  unfold AbsForest.Sfix
  rw [hC]
  congr 1
  apply Finset.filter_congr
  intro u _
  constructor
  · rintro ⟨p, hp, hw, h⟩
    have ht : p.1 ∈ H.Ctree φ₀ s ∨ p.2 ∈ H.Ctree φ₀ s := by
      rcases h with h | h
      · exact Or.inl h.1
      · exact Or.inr h.1
    exact ⟨p, hp, (weld_iff_of_agree_sfix H hH φ φ₀ s hφ p hp ht).mp hw, h⟩
  · rintro ⟨p, hp, hw, h⟩
    have ht : p.1 ∈ H.Ctree φ₀ s ∨ p.2 ∈ H.Ctree φ₀ s := by
      rcases h with h | h
      · exact Or.inl h.1
      · exact Or.inr h.1
    exact ⟨p, hp, (weld_iff_of_agree_sfix H hH φ φ₀ s hφ p hp ht).mpr hw, h⟩

lemma wfix_eq_of_agree_sfix (H : AbsForest n) (hH : H.IsValid)
    (φ φ₀ : Fin H.k → Label n) (s : Fin H.k)
    (hφ : ∀ u ∈ H.Sfix φ₀ s, φ u = φ₀ u) : H.Wfix φ s = H.Wfix φ₀ s := by
  classical
  have hC := ctree_eq_of_agree_sfix H hH φ φ₀ s hφ
  have hS := sfix_eq_of_agree_sfix H hH φ φ₀ s hφ
  unfold AbsForest.Wfix
  rw [hC, hS]
  congr 2
  · apply Finset.image_congr
    intro u hu
    exact congrArg (fun x : Label n => (u, x.val)) (hφ u (ctree_subset_sfix H φ₀ s hu))
  · apply Finset.image_congr
    intro u hu
    exact congrArg (fun x : Label n => (u, x.val)) (hφ u (Finset.mem_sdiff.mp hu).1)

lemma eq_on_of_image_graph_eq {V X : Type*} [DecidableEq V] [DecidableEq X]
    (A B : Finset V) (f g : V → X)
    (h : A.image (fun v => (v, f v)) = B.image (fun v => (v, g v))) :
    ∀ u ∈ B, f u = g u := by
  intro u hu
  have hm : (u, g u) ∈ A.image (fun v => (v, f v)) := by
    rw [h]
    exact Finset.mem_image.mpr ⟨u, hu, rfl⟩
  obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hm
  have hvu : v = u := congrArg Prod.fst hv
  subst v
  exact congrArg Prod.snd hv

/-- Fixed data is exactly a coordinate-fixing event on its recorded fixed
set. This is valid for all assignments, including those with zero reference
weight; no probabilistic conditioning assumption is hidden in the statement. -/
theorem wfix_eq_iff_agree_sfix (H : AbsForest n) (hH : H.IsValid)
    (φ φ₀ : Fin H.k → Label n) (s : Fin H.k) :
    H.Wfix φ s = H.Wfix φ₀ s ↔ ∀ u ∈ H.Sfix φ₀ s, φ u = φ₀ u := by
  classical
  constructor
  · intro hw u hu
    have hC := congrArg (fun t => t.2.1) hw
    have hS := congrArg (fun t => t.2.2) hw
    apply Fin.ext
    by_cases huc : u ∈ H.Ctree φ₀ s
    · exact eq_on_of_image_graph_eq _ _ (fun v => (φ v).val) (fun v => (φ₀ v).val) hC u huc
    · exact eq_on_of_image_graph_eq _ _ (fun v => (φ v).val) (fun v => (φ₀ v).val) hS u
        (Finset.mem_sdiff.mpr ⟨hu, huc⟩)
  · exact wfix_eq_of_agree_sfix H hH φ φ₀ s

/-- The fixed-data and boundary conditions of a description are local
restrictions on individual vertex labels. Injectivity is deliberately not
included: it is the separate collision condition in the good space. -/
def coordinateCondition (D : Description n) (B : Finset ℕ) (u : Fin D.H.k)
    (x : Label n) : Prop :=
  (∀ s ∈ D.sel, u ∈ D.H.Sfix D.ϕ₀ s → x = D.ϕ₀ u) ∧
  (∀ s ∈ D.sel, D.H.graph.Reachable s u →
    u ∉ D.H.Ctree D.ϕ₀ s → x.val ∉ B)

theorem description_conditions_iff (D : Description n) (hD : D.IsValid)
    (B : Finset ℕ) (φ : Fin D.H.k → Label n) :
    ((∀ s ∈ D.sel, D.H.Wfix φ s = D.H.Wfix D.ϕ₀ s) ∧
      (∀ s ∈ D.sel, ∀ u, D.H.graph.Reachable s u →
        u ∉ D.H.Ctree φ s → (φ u).val ∉ B)) ↔
      ∀ u, coordinateCondition D B u (φ u) := by
  constructor
  · rintro ⟨hw, hb⟩ u
    constructor
    · intro s hs hu
      exact (wfix_eq_iff_agree_sfix D.H hD.1 φ D.ϕ₀ s).mp (hw s hs) u hu
    · intro s hs hr hu
      have hC : D.H.Ctree φ s = D.H.Ctree D.ϕ₀ s := congrArg Prod.fst (hw s hs)
      exact hb s hs u hr (hC.symm ▸ hu)
  · intro h
    have hw : ∀ s ∈ D.sel, D.H.Wfix φ s = D.H.Wfix D.ϕ₀ s := by
      intro s hs
      apply (wfix_eq_iff_agree_sfix D.H hD.1 φ D.ϕ₀ s).mpr
      intro u hu
      exact (h u).1 s hs hu
    refine ⟨hw, ?_⟩
    intro s hs u hr hu
    have hC : D.H.Ctree φ s = D.H.Ctree D.ϕ₀ s := congrArg Prod.fst (hw s hs)
    exact (h u).2 s hs hr (hC ▸ hu)

theorem isGood_iff_coordinateCondition (l : ℕ) (G : WeldedInstance n)
    (D : Description n) (hD : D.IsValid) (B : Finset ℕ) (φ : Fin D.H.k → Label n) :
    D.IsGood l G B φ ↔
      0 < D.H.muRef l G φ ∧ (∀ u, coordinateCondition D B u (φ u)) ∧
        Function.Injective φ := by
  constructor
  · rintro ⟨hμ, hw, hb, hi⟩
    exact ⟨hμ, (description_conditions_iff D hD B φ).mp ⟨hw, hb⟩, hi⟩
  · rintro ⟨hμ, hc, hi⟩
    obtain ⟨hw, hb⟩ := (description_conditions_iff D hD B φ).mpr hc
    exact ⟨hμ, hw, hb, hi⟩

end WeldedPath.Supplement.FixedData

end

-- Solutions.FiniteRankEnumeration
section

namespace FiniteRankEnumeration

/-- A finite set can be enumerated in increasing rank, with arbitrary but
consistent tie breaking. Strict rank inequalities become strict index inequalities. -/
theorem exists_rank_order {S : Type*} [Fintype S] (rank : S → ℕ) :
    ∃ order : Fin (Fintype.card S) ≃ S,
      ∀ i j, rank (order i) < rank (order j) → i < j := by
  classical
  let key : S → Lex (ℕ × Fin (Fintype.card S)) :=
    fun x => toLex (rank x, Fintype.equivFin S x)
  have hinj : Function.Injective key := by
    intro x y h
    apply (Fintype.equivFin S).injective
    exact congrArg (fun z : Lex (ℕ × Fin (Fintype.card S)) => (ofLex z).2) h
  letI : LinearOrder S := LinearOrder.lift' key hinj
  let order := Fintype.orderIsoFinOfCardEq S rfl
  refine ⟨order.toEquiv, ?_⟩
  intro i j hij
  have hlt : order i < order j := by
    change key (order i) < key (order j)
    exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl hij)
  exact order.lt_iff_lt.mp hlt

theorem exists_rank_order_of_card_eq {S : Type*} [Fintype S] (rank : S → ℕ)
    (k : ℕ) (hk : Fintype.card S = k) :
    ∃ order : Fin k ≃ S, ∀ i j, rank (order i) < rank (order j) → i < j := by
  subst k
  exact exists_rank_order rank

end FiniteRankEnumeration

end

-- Solutions.WeldedPathForestOrder
section

namespace WeldedPath.Supplement.ForestOrder

open Classical

section RootedForest

variable {V : Type*} (J : SimpleGraph V) (s : V)

theorem lower_neighbor_exists {v : V} (hr : J.Reachable s v) (hne : v ≠ s) :
    ∃ w, J.Adj v w ∧ J.dist s w + 1 = J.dist s v := by
  obtain ⟨p, hp⟩ := hr.symm.exists_walk_length_eq_dist
  cases p with
  | nil => exact (hne rfl).elim
  | @cons v w s h q =>
    refine ⟨w, h, ?_⟩
    have hq := J.dist_le q
    have ht := h.reachable.dist_triangle_left s
    have he : J.dist v w = 1 := J.dist_eq_one_iff_adj.mpr h
    simp only [SimpleGraph.Walk.length_cons] at hp
    rw [J.dist_comm (u := v) (v := s)] at hp
    rw [J.dist_comm (u := w) (v := s)] at hq
    rw [J.dist_comm (u := v) (v := s), J.dist_comm (u := w) (v := s)] at ht
    rw [he] at ht
    omega

noncomputable def rootParent (v : V) : V :=
  if h : J.Reachable s v ∧ v ≠ s then Classical.choose (lower_neighbor_exists J s h.1 h.2)
  else s

theorem rootParent_spec {v : V} (hr : J.Reachable s v) (hne : v ≠ s) :
    J.Adj v (rootParent J s v) ∧ J.dist s (rootParent J s v) + 1 = J.dist s v := by
  rw [rootParent, dif_pos ⟨hr, hne⟩]
  exact Classical.choose_spec (lower_neighbor_exists J s hr hne)

theorem lower_neighbor_unique (hJ : J.IsAcyclic) {v w w' : V}
    (hv : J.Reachable s v) (hw : J.Adj v w) (hw' : J.Adj v w')
    (hd : J.dist s w + 1 = J.dist s v) (hd' : J.dist s w' + 1 = J.dist s v) : w = w' := by
  obtain ⟨p, hp, hplen⟩ := (hv.trans hw.reachable).symm.exists_path_of_dist
  obtain ⟨q, hq, hqlen⟩ := (hv.trans hw'.reachable).symm.exists_path_of_dist
  have hpl : (p.cons hw).length = J.dist v s := by
    simp only [SimpleGraph.Walk.length_cons, hplen]
    rw [J.dist_comm (u := w) (v := s), J.dist_comm (u := v) (v := s)]
    omega
  have hql : (q.cons hw').length = J.dist v s := by
    simp only [SimpleGraph.Walk.length_cons, hqlen]
    rw [J.dist_comm (u := w') (v := s), J.dist_comm (u := v) (v := s)]
    omega
  have heq : p.cons hw = q.cons hw' := Subtype.mk.inj <|
    (hJ.subsingleton_path v s).elim
      ⟨p.cons hw, (p.cons hw).isPath_of_length_eq_dist hpl⟩
      ⟨q.cons hw', (q.cons hw').isPath_of_length_eq_dist hql⟩
  simpa only [SimpleGraph.Walk.snd_cons] using congrArg SimpleGraph.Walk.snd heq

theorem eq_rootParent_of_lower (hJ : J.IsAcyclic) {v w : V}
    (hv : J.Reachable s v) (hw : J.Adj v w)
    (hd : J.dist s w + 1 = J.dist s v) : w = rootParent J s v := by
  have hne : v ≠ s := by intro h; subst v; simp at hd
  have hs := rootParent_spec J s hv hne
  exact lower_neighbor_unique J s hJ hv hw hs.1 hd hs.2

theorem adjacent_parent_cases (hJ : J.IsAcyclic) {u v : V}
    (hu : J.Reachable s u) (h : J.Adj u v) :
    rootParent J s u = v ∨ rootParent J s v = u := by
  rcases hJ.dist_eq_dist_add_one_of_adj_of_reachable s h hu with hd | hd
  · exact Or.inl (eq_rootParent_of_lower J s hJ hu h hd.symm).symm
  · exact Or.inr (eq_rootParent_of_lower J s hJ (hu.trans h.reachable) h.symm hd.symm).symm

theorem lower_neighbor_mem_of_path (hJ : J.IsAcyclic) (S : Set V)
    {v w : V} (hv : J.Reachable s v) (hw : J.Adj v w)
    (hd : J.dist s w + 1 = J.dist s v)
    (p : J.Walk v s) (hp : p.IsPath) (hS : ∀ x ∈ p.support, x ∈ S) : w ∈ S := by
  obtain ⟨q, hq, hqlen⟩ := (hv.trans hw.reachable).symm.exists_path_of_dist
  have hlen : (q.cons hw).length = J.dist v s := by
    simp only [SimpleGraph.Walk.length_cons, hqlen]
    rw [J.dist_comm (u := w) (v := s), J.dist_comm (u := v) (v := s)]
    omega
  have heq : q.cons hw = p := Subtype.mk.inj <|
    (hJ.subsingleton_path v s).elim
      ⟨q.cons hw, (q.cons hw).isPath_of_length_eq_dist hlen⟩ ⟨p, hp⟩
  apply hS
  rw [← heq]
  simp only [SimpleGraph.Walk.support_cons, List.mem_cons]
  exact Or.inr q.start_mem_support

end RootedForest

variable {n : ℕ} (H : AbsForest n) (hH : H.IsValid)
  (φ : Fin H.k → Label n) (s : Fin H.k)

lemma treeGraph_le : H.treeGraph φ ≤ H.graph := by
  rintro u v ⟨hne, h | h⟩
  · exact ⟨hne, Or.inl h.1⟩
  · exact ⟨hne, Or.inr h.1⟩

lemma root_mem_ctree : s ∈ H.Ctree φ s := by
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, SimpleGraph.Reachable.refl _⟩

lemma root_mem_sfix : s ∈ H.Sfix φ s :=
  FixedData.ctree_subset_sfix H φ s (root_mem_ctree H φ s)

lemma ctree_path {v : Fin H.k} (hv : v ∈ H.Ctree φ s) :
    ∃ p : H.graph.Walk v s, p.IsPath ∧ ∀ x ∈ p.support, x ∈ H.Ctree φ s := by
  classical
  have hr : (H.treeGraph φ).Reachable s v := (Finset.mem_filter.mp hv).2
  obtain ⟨p, hp⟩ := hr.symm.exists_isPath
  refine ⟨p.mapLe (treeGraph_le H φ), hp.mapLe _, ?_⟩
  intro x hx
  rw [SimpleGraph.Walk.support_mapLe_eq_support] at hx
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr.trans (p.takeUntil x hx).reachable⟩

include hH in
lemma sfix_path {v : Fin H.k} (hv : v ∈ H.Sfix φ s) :
    ∃ p : H.graph.Walk v s, p.IsPath ∧ ∀ x ∈ p.support, x ∈ H.Sfix φ s := by
  classical
  by_cases hc : v ∈ H.Ctree φ s
  · obtain ⟨p, hp, hps⟩ := ctree_path H φ s hc
    exact ⟨p, hp, fun x hx => FixedData.ctree_subset_sfix H φ s (hps x hx)⟩
  · obtain ⟨e, he, hw, hor⟩ := (Finset.mem_filter.mp
      ((Finset.mem_union.mp hv).resolve_left hc)).2
    have hegraph : H.graph.Adj e.1 e.2 :=
      ⟨ne_of_lt (hH.1 e he), Or.inl he⟩
    have hex : ∃ w, w ∈ H.Ctree φ s ∧ H.graph.Adj v w := by
      rcases hor with ⟨hec, hev⟩ | ⟨hec, hev⟩
      · exact ⟨e.1, hec, hev ▸ hegraph.symm⟩
      · exact ⟨e.2, hec, hev ▸ hegraph⟩
    obtain ⟨w, hwc, hvw⟩ := hex
    obtain ⟨p, hp, hps⟩ := ctree_path H φ s hwc
    refine ⟨p.cons hvw, (SimpleGraph.Walk.cons_isPath_iff _ _).mpr
      ⟨hp, fun hvp => hc (hps v hvp)⟩, ?_⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hv
    · exact FixedData.ctree_subset_sfix H φ s (hps x hx)

include hH in
lemma sfix_subset_comp : H.Sfix φ s ⊆ H.comp s := by
  intro v hv
  obtain ⟨p, _, _⟩ := sfix_path H hH φ s hv
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, p.reachable.symm⟩

include hH in
lemma parent_mem_sfix {v : Fin H.k} (hv : v ∈ H.Sfix φ s) :
    rootParent H.graph s v ∈ H.Sfix φ s := by
  classical
  by_cases hvs : v = s
  · subst v
    simp only [rootParent, ne_eq, not_true_eq_false, and_false, dite_false]
    exact root_mem_sfix H φ s
  · obtain ⟨p, hp, hps⟩ := sfix_path H hH φ s hv
    have hr := p.reachable.symm
    have hs := rootParent_spec H.graph s hr hvs
    exact lower_neighbor_mem_of_path H.graph s hH.2.1
      (↑(H.Sfix φ s)) hr hs.1 hs.2 p hp hps

lemma sfix_not_ctree_weld {v : Fin H.k}
    (hv : v ∈ H.Sfix φ s) (hc : v ∉ H.Ctree φ s) : (φ v).val ∈ Vweld n := by
  classical
  obtain ⟨e, he, hw, hor⟩ := (Finset.mem_filter.mp
    ((Finset.mem_union.mp hv).resolve_left hc)).2
  rcases hor with ⟨_, hev⟩ | ⟨_, hev⟩
  · exact hev ▸ hw.2
  · exact hev ▸ hw.1

include hH in
lemma free_parent_fixed_weld {v : Fin H.k}
    (hv : v ∈ H.comp s) (hf : v ∉ H.Sfix φ s)
    (hp : rootParent H.graph s v ∈ H.Sfix φ s) :
    (φ (rootParent H.graph s v)).val ∈ Vweld n := by
  have hvs : v ≠ s := by
    intro heq
    apply hf
    rw [heq]
    exact root_mem_sfix H φ s
  have hs := rootParent_spec H.graph s (Finset.mem_filter.mp hv).2 hvs
  apply sfix_not_ctree_weld H φ s hp
  intro hc
  rcases hs.1.2 with he | he
  · exact hf (FixedData.edge_endpoints_mem_sfix H hH φ s _ he (Or.inr hc)).1
  · exact hf (FixedData.edge_endpoints_mem_sfix H hH φ s _ he (Or.inl hc)).2

noncomputable def freeVertices : Finset (Fin H.k) := H.comp s \ H.Sfix φ s

noncomputable def freeEdges : Finset (Fin H.k × Fin H.k) :=
  H.E.filter (fun e => e.1 ∈ H.comp s ∧
    ¬(e.1 ∈ H.Sfix φ s ∧ e.2 ∈ H.Sfix φ s))

lemma free_vertex_spec (v : freeVertices H φ s) :
    (v : Fin H.k) ∈ H.comp s ∧ (v : Fin H.k) ∉ H.Sfix φ s :=
  Finset.mem_sdiff.mp v.property

lemma free_parent_spec (v : freeVertices H φ s) :
    H.graph.Adj v (rootParent H.graph s v) ∧
    H.graph.dist s (rootParent H.graph s v) + 1 = H.graph.dist s v := by
  apply rootParent_spec H.graph s (Finset.mem_filter.mp (free_vertex_spec H φ s v).1).2
  intro heq
  apply (free_vertex_spec H φ s v).2
  rw [heq]
  exact root_mem_sfix H φ s

lemma free_parent_mem_comp (v : freeVertices H φ s) :
    rootParent H.graph s v ∈ H.comp s := by
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _, (Finset.mem_filter.mp (free_vertex_spec H φ s v).1).2.trans
    (free_parent_spec H φ s v).1.reachable⟩

noncomputable def parentEdge (v : freeVertices H φ s) : Fin H.k × Fin H.k :=
  if (v : Fin H.k) < rootParent H.graph s v then (v, rootParent H.graph s v)
  else (rootParent H.graph s v, v)

include hH in
lemma parentEdge_mem (v : freeVertices H φ s) : parentEdge H φ s v ∈ freeEdges H φ s := by
  classical
  have hs := free_parent_spec H φ s v
  have hf := free_vertex_spec H φ s v
  have hp := free_parent_mem_comp H φ s v
  unfold parentEdge
  split_ifs with hlt
  · apply Finset.mem_filter.mpr
    refine ⟨?_, hf.1, fun hx => hf.2 hx.1⟩
    rcases hs.1.2 with he | he
    · exact he
    · have hh := hH.1 _ he; exact (not_lt_of_ge (le_of_lt hlt) hh).elim
  · apply Finset.mem_filter.mpr
    refine ⟨?_, hp, fun hx => hf.2 hx.2⟩
    rcases hs.1.2 with he | he
    · exact (hlt (hH.1 _ he)).elim
    · exact he

lemma parentEdge_injective : Function.Injective (parentEdge H φ s) := by
  classical
  intro v w heq
  have hv := (free_parent_spec H φ s v).2
  have hw := (free_parent_spec H φ s w).2
  unfold parentEdge at heq
  split_ifs at heq with h₁ h₂ h₂
  · exact Subtype.ext (congrArg Prod.fst heq)
  · have ha := congrArg Prod.fst heq
    have hb := congrArg Prod.snd heq
    dsimp only at ha hb
    have hra := congrArg (H.graph.dist s) ha
    have hrb := congrArg (H.graph.dist s) hb
    omega
  · have ha := congrArg Prod.fst heq
    have hb := congrArg Prod.snd heq
    dsimp only at ha hb
    have hra := congrArg (H.graph.dist s) ha
    have hrb := congrArg (H.graph.dist s) hb
    omega
  · exact Subtype.ext (congrArg Prod.snd heq)

noncomputable def edgeOfFree (v : freeVertices H φ s) : freeEdges H φ s :=
  ⟨parentEdge H φ s v, parentEdge_mem H hH φ s v⟩

lemma edgeOfFree_bijective : Function.Bijective (edgeOfFree H hH φ s) := by
  classical
  constructor
  · intro v w heq
    exact parentEdge_injective H φ s (congrArg Subtype.val heq)
  · intro e
    have he := Finset.mem_filter.mp e.property
    have hadj : H.graph.Adj e.val.1 e.val.2 := ⟨ne_of_lt (hH.1 _ he.1), Or.inl he.1⟩
    have hr := (Finset.mem_filter.mp he.2.1).2
    have hr' : e.val.2 ∈ H.comp s :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr.trans hadj.reachable⟩
    rcases adjacent_parent_cases H.graph s hH.2.1 hr hadj with hp | hp
    · have hf : e.val.1 ∉ H.Sfix φ s := by
        intro hc
        exact he.2.2 ⟨hc, hp ▸ parent_mem_sfix H hH φ s hc⟩
      let v : freeVertices H φ s := ⟨e.val.1, Finset.mem_sdiff.mpr ⟨he.2.1, hf⟩⟩
      refine ⟨v, Subtype.ext ?_⟩
      change parentEdge H φ s v = e.val
      have hlt := hH.1 _ he.1
      simp only [parentEdge, v, hp, if_pos hlt]
    · have hf : e.val.2 ∉ H.Sfix φ s := by
        intro hc
        exact he.2.2 ⟨hp ▸ parent_mem_sfix H hH φ s hc, hc⟩
      let v : freeVertices H φ s := ⟨e.val.2, Finset.mem_sdiff.mpr ⟨hr', hf⟩⟩
      refine ⟨v, Subtype.ext ?_⟩
      change parentEdge H φ s v = e.val
      have hlt := not_lt_of_gt (hH.1 _ he.1)
      simp only [parentEdge, v, hp, if_neg hlt]

noncomputable def freeEdgeEquiv : freeVertices H φ s ≃ freeEdges H φ s :=
  Equiv.ofBijective (edgeOfFree H hH φ s) (edgeOfFree_bijective H hH φ s)

def parentVertex {m : ℕ} (order : Fin m → Fin H.k) (fixed : Fin m → Fin H.k)
    (parent : (i : Fin m) → Option (Fin i.val)) (i : Fin m) : Fin H.k :=
  match parent i with
  | none => fixed i
  | some j => order ⟨j.val, lt_trans j.isLt i.isLt⟩

/-- Every free vertex is enumerated after its parent. Every edge outside the
fixed set occurs once, and every fixed parent has a weld label. -/
structure ParentOrder where
  order : Fin (Fintype.card ↥(freeVertices H φ s)) ≃ freeVertices H φ s
  parent : (i : Fin (Fintype.card ↥(freeVertices H φ s))) → Option (Fin i.val)
  fixed : Fin (Fintype.card ↥(freeVertices H φ s)) → Fin H.k
  edge : Fin (Fintype.card ↥(freeVertices H φ s)) ≃ freeEdges H φ s
  edge_endpoints : ∀ i,
    (edge i).val = ((order i).val, parentVertex H (fun j => (order j).val) fixed parent i) ∨
    (edge i).val = (parentVertex H (fun j => (order j).val) fixed parent i, (order i).val)
  fixed_mem : ∀ i, parent i = none → fixed i ∈ H.Sfix φ s
  fixed_weld : ∀ i, parent i = none → (φ (fixed i)).val ∈ Vweld n

include hH in
theorem exists_parent_order : Nonempty (ParentOrder H φ s) := by
  classical
  have ho : ∃ order : Fin (Fintype.card ↥(freeVertices H φ s)) ≃ freeVertices H φ s,
      ∀ i j, H.graph.dist s (order i).val < H.graph.dist s (order j).val → i < j := by
    exact FiniteRankEnumeration.exists_rank_order
      (fun v : freeVertices H φ s => H.graph.dist s v.val)
  obtain ⟨order, hord⟩ := ho
  let fixed : Fin (Fintype.card ↥(freeVertices H φ s)) → Fin H.k :=
    fun i => rootParent H.graph s (order i)
  have hparent (i : Fin (Fintype.card ↥(freeVertices H φ s))) :
      ∃ p : Option (Fin i.val),
        (match p with
         | none => fixed i
         | some j => (order ⟨j.val, lt_trans j.isLt i.isLt⟩).val) = fixed i ∧
        (p = none → fixed i ∈ H.Sfix φ s ∧ (φ (fixed i)).val ∈ Vweld n) := by
    by_cases hp : fixed i ∈ H.Sfix φ s
    · refine ⟨none, rfl, fun _ => ⟨hp, ?_⟩⟩
      exact free_parent_fixed_weld H hH φ s (free_vertex_spec H φ s (order i)).1
        (free_vertex_spec H φ s (order i)).2 hp
    · let v : freeVertices H φ s :=
        ⟨fixed i, Finset.mem_sdiff.mpr ⟨free_parent_mem_comp H φ s (order i), hp⟩⟩
      have hlt : order.symm v < i := by
        apply hord
        simp only [Equiv.apply_symm_apply]
        have hd := (free_parent_spec H φ s (order i)).2
        change H.graph.dist s (fixed i) + 1 = H.graph.dist s (order i).val at hd
        change H.graph.dist s (fixed i) < H.graph.dist s (order i).val
        omega
      refine ⟨some ⟨(order.symm v).val, hlt⟩, ?_, by simp⟩
      change (order (order.symm v)).val = fixed i
      simp only [Equiv.apply_symm_apply]
      rfl
  let parent (i : Fin (Fintype.card ↥(freeVertices H φ s))) : Option (Fin i.val) :=
    Classical.choose (hparent i)
  have hspec i := Classical.choose_spec (hparent i)
  refine ⟨{
    order := order
    parent := parent
    fixed := fixed
    edge := order.trans (freeEdgeEquiv H hH φ s)
    edge_endpoints := ?_
    fixed_mem := fun i hi => ((hspec i).2 hi).1
    fixed_weld := fun i hi => ((hspec i).2 hi).2 }⟩
  intro i
  have hp : parentVertex H (fun j => (order j).val) fixed parent i = fixed i := by
    unfold parentVertex parent
    convert (hspec i).1 using 1
    cases Classical.choose (hparent i) <;> rfl
  change parentEdge H φ s (order i) = ((order i).val, _) ∨
    parentEdge H φ s (order i) = (_, (order i).val)
  rw [hp]
  unfold parentEdge
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

end WeldedPath.Supplement.ForestOrder

end

-- Solutions.WeightedForestFactorization
section

/-! Finite weighted laws split by a separator.  All identities also cover zero
normalizers: division is the ordinary totalized division on `ℝ`. -/

namespace FiniteWeightedForest

open scoped BigOperators

section ProductLaws

variable {Ω A B : Type*} [Fintype Ω] [Fintype A] [Fintype B]

/-- Reindexing a product of two finite weights factors its normalizer. -/
theorem sum_factor {R : Type*} [CommSemiring R]
    (e : Ω ≃ A × B) (f : A → R) (g : B → R) :
    (∑ ω, f (e ω).1 * g (e ω).2) = (∑ a, f a) * ∑ b, g b := by
  rw [Fintype.sum_equiv e _ (fun p => f p.1 * g p.2) (fun _ => rfl)]
  rw [Fintype.sum_prod_type, Fintype.sum_mul_sum]

/-- A centered function of one branch is orthogonal to every function of the
other branch. With `R = ℂ`, the first function may include complex conjugation. -/
theorem weighted_centered_sum {R : Type*} [CommSemiring R]
    (e : Ω ≃ A × B) (f u : A → R) (g v : B → R)
    (hu : ∑ a, f a * u a = 0) :
    (∑ ω, f (e ω).1 * g (e ω).2 * (u (e ω).1 * v (e ω).2)) = 0 := by
  calc
    _ = ∑ ω, (f (e ω).1 * u (e ω).1) * (g (e ω).2 * v (e ω).2) := by
      apply Finset.sum_congr rfl
      intro ω _
      ring
    _ = (∑ a, f a * u a) * ∑ b, g b * v b :=
      sum_factor e (fun a => f a * u a) (fun b => g b * v b)
    _ = 0 := by rw [hu, zero_mul]

/-- A constant shared factor cancels from a normalized finite law. -/
theorem normalize_scale (w : Ω → ℝ) (c : ℝ) (hc : c ≠ 0) (ω : Ω) :
    (c * w ω) / (∑ η, c * w η) = w ω / ∑ η, w η := by
  rw [← Finset.mul_sum]
  exact mul_div_mul_left _ _ hc

/-- The normalized product law is the product of the normalized branch laws. -/
theorem normalize_factor (e : Ω ≃ A × B) (f : A → ℝ) (g : B → ℝ) (ω : Ω) :
    (f (e ω).1 * g (e ω).2) / (∑ η, f (e η).1 * g (e η).2) =
      (f (e ω).1 / ∑ a, f a) * (g (e ω).2 / ∑ b, g b) := by
  rw [sum_factor]
  exact (div_mul_div_comm _ _ _ _).symm

/-- Conditional weights on a rectangular event remain a product law. -/
theorem conditional_factor (e : Ω ≃ A × B) (f : A → ℝ) (g : B → ℝ)
    (P : A → Prop) (Q : B → Prop) [DecidablePred P] [DecidablePred Q] (ω : Ω) :
    (if P (e ω).1 ∧ Q (e ω).2 then f (e ω).1 * g (e ω).2 else 0) /
      (∑ η, if P (e η).1 ∧ Q (e η).2 then f (e η).1 * g (e η).2 else 0) =
      ((if P (e ω).1 then f (e ω).1 else 0) /
        ∑ a, if P a then f a else 0) *
      ((if Q (e ω).2 then g (e ω).2 else 0) /
        ∑ b, if Q b then g b else 0) := by
  have h (a : A) (b : B) :
      (if P a ∧ Q b then f a * g b else 0) =
        (if P a then f a else 0) * (if Q b then g b else 0) := by
    split_ifs <;> simp_all
  simp_rw [h]
  exact normalize_factor e (fun a => if P a then f a else 0)
    (fun b => if Q b then g b else 0) ω

/-- Fixing the two endpoints of a bridge makes its kernel a constant, so the
two sides are conditionally independent. No positivity assumptions are needed
apart from the bridge value being nonzero. -/
theorem bridge_conditional_factor {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    (e : Ω ≃ A × B) (f : A → ℝ) (g : B → ℝ)
    (left : A → X) (right : B → Y) (K : X → Y → ℝ)
    (x : X) (y : Y) (hK : K x y ≠ 0) (ω : Ω) :
    (if left (e ω).1 = x ∧ right (e ω).2 = y then
        f (e ω).1 * g (e ω).2 * K (left (e ω).1) (right (e ω).2) else 0) /
      (∑ η, if left (e η).1 = x ∧ right (e η).2 = y then
        f (e η).1 * g (e η).2 * K (left (e η).1) (right (e η).2) else 0) =
      ((if left (e ω).1 = x then f (e ω).1 else 0) /
        ∑ a, if left a = x then f a else 0) *
      ((if right (e ω).2 = y then g (e ω).2 else 0) /
        ∑ b, if right b = y then g b else 0) := by
  have h (η : Ω) :
      (if left (e η).1 = x ∧ right (e η).2 = y then
        f (e η).1 * g (e η).2 * K (left (e η).1) (right (e η).2) else 0) =
      K x y * (if left (e η).1 = x ∧ right (e η).2 = y then
        f (e η).1 * g (e η).2 else 0) := by
    by_cases hxy : left (e η).1 = x ∧ right (e η).2 = y
    · simp [hxy, hxy.1, hxy.2, mul_comm]
    · simp [hxy]
  simp_rw [h]
  rw [normalize_scale (fun η => if left (e η).1 = x ∧ right (e η).2 = y then
    f (e η).1 * g (e η).2 else 0) _ hK]
  exact conditional_factor e f g (fun a => left a = x) (fun b => right b = y) ω

end ProductLaws

section VertexPartition

variable {V X : Type*} [Fintype V] [DecidableEq V] [Fintype X]

/-- Restrict an assignment to the two sides of a finite vertex separator. -/
def splitAssignment (S : Finset V) :
    (V → X) ≃ (({v // v ∈ S} → X) × ({v // v ∉ S} → X)) :=
  Equiv.piEquivPiSubtypeProd (fun v => v ∈ S) (fun _ => X)

@[simp] theorem splitAssignment_left (S : Finset V) (φ : V → X) (u : {v // v ∈ S}) :
    (splitAssignment S φ).1 u = φ u := rfl

@[simp] theorem splitAssignment_right (S : Finset V) (φ : V → X) (u : {v // v ∉ S}) :
    (splitAssignment S φ).2 u = φ u := rfl

theorem sum_split (S : Finset V) (f : ({v // v ∈ S} → X) → ℝ)
    (g : ({v // v ∉ S} → X) → ℝ) :
    (∑ φ : V → X, f (fun u => φ u) * g (fun u => φ u)) =
      (∑ a, f a) * ∑ b, g b :=
  sum_factor (splitAssignment S) f g

end VertexPartition

section EdgeProducts

variable {V X : Type*} [DecidableEq V]

/-- A product of possibly edge-dependent transition weights. -/
noncomputable def edgeWeight (E : Finset (V × V)) (K : (V × V) → X → X → ℝ)
    (φ : V → X) : ℝ := ∏ p ∈ E, K p (φ p.1) (φ p.2)

/-- Deleting one stored edge removes exactly its kernel factor. -/
theorem edgeWeight_erase (E : Finset (V × V)) (K : (V × V) → X → X → ℝ)
    (φ : V → X) (e : V × V) (he : e ∈ E) :
    edgeWeight E K φ = edgeWeight (E.erase e) K φ * K e (φ e.1) (φ e.2) := by
  classical
  exact (Finset.prod_erase_mul E (fun p => K p (φ p.1) (φ p.2)) he).symm

/-- The remaining product separates by the side containing the first endpoint.
For a graph separator, both endpoints of every remaining edge lie on this side. -/
theorem edgeWeight_split (E : Finset (V × V)) (S : Finset V)
    (K : (V × V) → X → X → ℝ) (φ : V → X) :
    edgeWeight E K φ =
      edgeWeight (E.filter (fun p => p.1 ∈ S)) K φ *
      edgeWeight (E.filter (fun p => p.1 ∉ S)) K φ := by
  classical
  exact (Finset.prod_filter_mul_prod_filter_not E (fun p => p.1 ∈ S)
    (fun p => K p (φ p.1) (φ p.2))).symm

/-- Exact one-edge separator factorization of an arbitrary edge-weight product. -/
theorem edgeWeight_bridge (E : Finset (V × V)) (S : Finset V)
    (K : (V × V) → X → X → ℝ) (φ : V → X) (e : V × V) (he : e ∈ E) :
    edgeWeight E K φ =
      edgeWeight ((E.erase e).filter (fun p => p.1 ∈ S)) K φ *
      edgeWeight ((E.erase e).filter (fun p => p.1 ∉ S)) K φ *
      K e (φ e.1) (φ e.2) := by
  rw [edgeWeight_erase E K φ e he, edgeWeight_split (E.erase e) S K φ]

end EdgeProducts

end FiniteWeightedForest

end

-- Solutions.WeightedForestSeparator
section

namespace FiniteWeightedForest

open scoped BigOperators

section BranchWeights

variable {V X : Type*} [DecidableEq V] [Zero X]

/-- Extend a branch assignment by zero off that branch. Off-branch values do
not affect the branch weight when all its edges stay in the branch. -/
def extendAssignment (P : V → Prop) [DecidablePred P] (a : {v // P v} → X) (v : V) : X :=
  if h : P v then a ⟨v, h⟩ else 0

noncomputable def branchWeight (E : Finset (V × V)) (P : V → Prop) [DecidablePred P]
    (K : (V × V) → X → X → ℝ) (a : {v // P v} → X) : ℝ :=
  edgeWeight (E.filter (fun p => P p.1)) K (extendAssignment P a)

theorem branchWeight_restrict (E : Finset (V × V)) (P : V → Prop) [DecidablePred P]
    (K : (V × V) → X → X → ℝ) (φ : V → X)
    (hclosed : ∀ p ∈ E, P p.1 ↔ P p.2) :
    branchWeight E P K (fun v => φ v) =
      edgeWeight (E.filter (fun p => P p.1)) K φ := by
  classical
  unfold branchWeight edgeWeight
  apply Finset.prod_congr rfl
  intro p hp
  obtain ⟨hpE, hpP⟩ := Finset.mem_filter.mp hp
  simp [extendAssignment, hpP, (hclosed p hpE).mp hpP]

/-- An edge product on a graph with a one-edge separator is a product of its
two branch weights and the separating edge kernel. -/
theorem edgeWeight_bridge_branches (E : Finset (V × V)) (P : V → Prop)
    [DecidablePred P] (K : (V × V) → X → X → ℝ) (φ : V → X)
    (e : V × V) (he : e ∈ E)
    (hclosed : ∀ p ∈ E.erase e, P p.1 ↔ P p.2) :
    edgeWeight E K φ =
      branchWeight (E.erase e) P K (fun v => φ v) *
      branchWeight (E.erase e) (fun v => ¬P v) K (fun v => φ v) *
      K e (φ e.1) (φ e.2) := by
  classical
  rw [branchWeight_restrict _ P _ _ hclosed,
    branchWeight_restrict _ (fun v => ¬P v) _ _ (fun p hp => not_congr (hclosed p hp)),
    edgeWeight_erase E K φ e he]
  congr 1
  exact (Finset.prod_filter_mul_prod_filter_not (E.erase e) (fun p => P p.1)
    (fun p => K p (φ p.1) (φ p.2))).symm

/-- Exact conditional independence of the branches of a weighted tree after
the values of the two endpoints of a deleted edge are fixed. -/
theorem tree_bridge_conditional_factor [Fintype V] [Fintype X] [DecidableEq X]
    (E : Finset (V × V)) (P : V → Prop) [DecidablePred P]
    (K : (V × V) → X → X → ℝ) (e : V × V) (he : e ∈ E)
    (hleft : P e.1) (hright : ¬P e.2)
    (hclosed : ∀ p ∈ E.erase e, P p.1 ↔ P p.2)
    (x y : X) (hK : K e x y ≠ 0) (φ : V → X) :
    (if φ e.1 = x ∧ φ e.2 = y then edgeWeight E K φ else 0) /
      (∑ ψ : V → X, if ψ e.1 = x ∧ ψ e.2 = y then edgeWeight E K ψ else 0) =
      ((if φ e.1 = x then branchWeight (E.erase e) P K (fun v => φ v) else 0) /
        ∑ a : {v // P v} → X,
          if a ⟨e.1, hleft⟩ = x then branchWeight (E.erase e) P K a else 0) *
      ((if φ e.2 = y then branchWeight (E.erase e) (fun v => ¬P v) K
          (fun v => φ v) else 0) /
        ∑ b : {v // ¬P v} → X,
          if b ⟨e.2, hright⟩ = y then branchWeight (E.erase e) (fun v => ¬P v) K b else 0) := by
  let split : (V → X) ≃ (({v // P v} → X) × ({v // ¬P v} → X)) :=
    Equiv.piEquivPiSubtypeProd P (fun _ => X)
  have hfactor (ψ : V → X) := edgeWeight_bridge_branches E P K ψ e he hclosed
  simp_rw [hfactor]
  exact bridge_conditional_factor split
    (branchWeight (E.erase e) P K) (branchWeight (E.erase e) (fun v => ¬P v) K)
    (fun a => a ⟨e.1, hleft⟩) (fun b => b ⟨e.2, hright⟩) (K e) x y hK φ

end BranchWeights

section SupportedWeights

variable {V X : Type*} [Fintype V] [DecidableEq V] [Fintype X] [Zero X]

/-- Edge-product weight with arbitrary restrictions at individual vertices. -/
noncomputable def forestWeight (E : Finset (V × V)) (K : (V × V) → X → X → ℝ)
    (allowed : V → X → Prop) (φ : V → X) : ℝ := by
  classical
  exact if ∀ v, allowed v (φ v) then edgeWeight E K φ else 0

noncomputable def supportedBranchWeight (E : Finset (V × V)) (P : V → Prop)
    [DecidablePred P] (K : (V × V) → X → X → ℝ) (allowed : V → X → Prop)
    (a : {v // P v} → X) : ℝ := by
  classical
  exact if ∀ v : {v // P v}, allowed v.val (a v) then branchWeight E P K a else 0

theorem forestWeight_bridge_branches (E : Finset (V × V)) (P : V → Prop)
    [DecidablePred P] (K : (V × V) → X → X → ℝ) (allowed : V → X → Prop)
    (φ : V → X) (e : V × V) (he : e ∈ E)
    (hclosed : ∀ p ∈ E.erase e, P p.1 ↔ P p.2) :
    forestWeight E K allowed φ =
      supportedBranchWeight (E.erase e) P K allowed (fun v => φ v) *
      supportedBranchWeight (E.erase e) (fun v => ¬P v) K allowed (fun v => φ v) *
      K e (φ e.1) (φ e.2) := by
  classical
  have hall : (∀ v, allowed v (φ v)) ↔
      (∀ v : {v // P v}, allowed v (φ v)) ∧
        (∀ v : {v // ¬P v}, allowed v (φ v)) := by
    constructor
    · intro h
      exact ⟨fun v => h v, fun v => h v⟩
    · rintro ⟨hl, hr⟩ v
      by_cases hv : P v
      · exact hl ⟨v, hv⟩
      · exact hr ⟨v, hv⟩
  unfold forestWeight supportedBranchWeight
  simp only [hall, edgeWeight_bridge_branches E P K φ e he hclosed,
    ite_and, mul_ite, ite_mul, mul_zero, zero_mul]
  split_ifs <;> rfl

/-- The separator law remains exact after imposing any local vertex support
conditions, including the allowed physical vertex set in `AbsForest.muComp`. -/
theorem supported_tree_bridge_conditional_factor [DecidableEq X]
    (E : Finset (V × V)) (P : V → Prop) [DecidablePred P]
    (K : (V × V) → X → X → ℝ) (allowed : V → X → Prop)
    (e : V × V) (he : e ∈ E) (hleft : P e.1) (hright : ¬P e.2)
    (hclosed : ∀ p ∈ E.erase e, P p.1 ↔ P p.2)
    (x y : X) (hK : K e x y ≠ 0) (φ : V → X) :
    (if φ e.1 = x ∧ φ e.2 = y then forestWeight E K allowed φ else 0) /
      (∑ ψ : V → X, if ψ e.1 = x ∧ ψ e.2 = y then forestWeight E K allowed ψ else 0) =
      ((if φ e.1 = x then supportedBranchWeight (E.erase e) P K allowed
          (fun v => φ v) else 0) /
        ∑ a : {v // P v} → X,
          if a ⟨e.1, hleft⟩ = x then supportedBranchWeight (E.erase e) P K allowed a else 0) *
      ((if φ e.2 = y then supportedBranchWeight (E.erase e) (fun v => ¬P v) K allowed
          (fun v => φ v) else 0) /
        ∑ b : {v // ¬P v} → X,
          if b ⟨e.2, hright⟩ = y then
            supportedBranchWeight (E.erase e) (fun v => ¬P v) K allowed b else 0) := by
  let split : (V → X) ≃ (({v // P v} → X) × ({v // ¬P v} → X)) :=
    Equiv.piEquivPiSubtypeProd P (fun _ => X)
  have hfactor (ψ : V → X) := forestWeight_bridge_branches E P K allowed ψ e he hclosed
  simp_rw [hfactor]
  exact bridge_conditional_factor split
    (supportedBranchWeight (E.erase e) P K allowed)
    (supportedBranchWeight (E.erase e) (fun v => ¬P v) K allowed)
    (fun a => a ⟨e.1, hleft⟩) (fun b => b ⟨e.2, hright⟩) (K e) x y hK φ

end SupportedWeights

section ForestCuts

variable {V : Type*} [LinearOrder V]

def edgeGraph (E : Finset (V × V)) : SimpleGraph V :=
  SimpleGraph.fromRel (fun u v => (u, v) ∈ E)

/-- With one increasing orientation per edge, erasing a stored pair deletes
the corresponding undirected edge. -/
theorem edgeGraph_erase_le_delete (E : Finset (V × V)) (e : V × V)
    (horder : ∀ p ∈ E, p.1 < p.2) (he : e ∈ E) :
    edgeGraph (E.erase e) ≤ (edgeGraph E).deleteEdges {s(e.1, e.2)} := by
  intro u v huv
  obtain ⟨hne, huv | hvu⟩ := huv
  · obtain ⟨hneq, hmem⟩ := Finset.mem_erase.mp huv
    apply SimpleGraph.deleteEdges_adj.mpr
    refine ⟨⟨hne, Or.inl hmem⟩, ?_⟩
    simp only [Set.mem_singleton_iff, Sym2.eq_iff]
    rintro (⟨hu, hv⟩ | ⟨hu, hv⟩)
    · exact hneq (Prod.ext hu hv)
    · have h := horder (u, v) hmem
      have heo := horder e he
      simp only [hu, hv] at h
      exact (lt_asymm h heo)
  · obtain ⟨hneq, hmem⟩ := Finset.mem_erase.mp hvu
    apply SimpleGraph.deleteEdges_adj.mpr
    refine ⟨⟨hne, Or.inr hmem⟩, ?_⟩
    simp only [Set.mem_singleton_iff, Sym2.eq_iff]
    rintro (⟨hu, hv⟩ | ⟨hu, hv⟩)
    · have h := horder (v, u) hmem
      have heo := horder e he
      simp only [hu, hv] at h
      exact (lt_asymm h heo)
    · exact hneq (Prod.ext hv hu)

/-- The endpoints of a forest edge belong to different components after it
is erased. -/
theorem forest_cut_not_reachable (E : Finset (V × V)) (e : V × V)
    (horder : ∀ p ∈ E, p.1 < p.2) (hforest : (edgeGraph E).IsAcyclic)
    (he : e ∈ E) : ¬(edgeGraph (E.erase e)).Reachable e.1 e.2 := by
  have hadj : (edgeGraph E).Adj e.1 e.2 := ⟨ne_of_lt (horder e he), Or.inl he⟩
  have hb := (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp hforest) hadj
  intro hr
  exact hb (hr.mono (edgeGraph_erase_le_delete E e horder he))

/-- No remaining edge crosses the component cut, so its kernel depends only
on the coordinates of one branch. -/
theorem forest_cut_closed (E : Finset (V × V)) (e : V × V)
    (horder : ∀ p ∈ E, p.1 < p.2) :
    ∀ p ∈ E.erase e,
      (edgeGraph (E.erase e)).Reachable e.1 p.1 ↔
        (edgeGraph (E.erase e)).Reachable e.1 p.2 := by
  intro p hp
  have hpE := (Finset.mem_erase.mp hp).2
  have hr : (edgeGraph (E.erase e)).Reachable p.1 p.2 :=
    SimpleGraph.Adj.reachable ⟨ne_of_lt (horder p hpE), Or.inl hp⟩
  exact ⟨fun h => h.trans hr, fun h => h.trans hr.symm⟩

end ForestCuts

end FiniteWeightedForest

end

-- Solutions.WeldedPathForestFactorization
section

namespace WeldedPath.Supplement.ForestFactorization

open scoped BigOperators
open FiniteWeightedForest

variable {n : ℕ}

noncomputable def componentEdges (H : AbsForest n) (s : Fin H.k) :
    Finset (Fin H.k × Fin H.k) := by
  classical
  exact H.E.filter (fun p => p.1 ∈ H.comp s)

noncomputable def componentKernel (l : ℕ) (G : WeldedInstance n) (H : AbsForest n)
    (p : Fin H.k × Fin H.k) (x y : Label n) : ℝ :=
  kappa l G (H.color p) x.val y.val

def componentAllowed (l : ℕ) (H : AbsForest n) (s u : Fin H.k) (x : Label n) : Prop :=
  u ∈ H.comp s → x.val ∈ Vmid n l ∪ Vbd n l

/-- The assignment-independent prefactor in the canonical definition of
`muComp` for a component with at least one edge. -/
noncomputable def componentScale (l : ℕ) (G : WeldedInstance n) (H : AbsForest n)
    (s : Fin H.k) : ℝ := by
  classical
  let V := Vmid n l ∪ Vbd n l
  let Z := (1 / (V.card : ℝ)) *
    ∑ ψ ∈ Finset.univ.filter (fun ψ : Fin H.k → Label n =>
      (∀ u ∈ H.comp s, (ψ u).val ∈ V) ∧ (∀ u, u ∉ H.comp s → ψ u = 0)),
        edgeWeight (componentEdges H s) (componentKernel l G H) ψ
  exact (1 / Z) * (1 / (V.card : ℝ))

/-- The canonical reference component measure is exactly a common scalar
times the edge-product law with its local vertex support restrictions. -/
theorem muComp_eq_scale_forestWeight (l : ℕ) (G : WeldedInstance n) (H : AbsForest n)
    (s : Fin H.k) (hsize : (H.comp s).card ≠ 1) (φ : Fin H.k → Label n) :
    H.muComp l G s φ = componentScale l G H s *
      forestWeight (componentEdges H s) (componentKernel l G H) (componentAllowed l H s) φ := by
  classical
  unfold AbsForest.muComp
  simp only [hsize, ite_false]
  unfold componentScale forestWeight componentAllowed componentEdges componentKernel edgeWeight
  simp only [mul_ite, mul_zero]

theorem componentScale_ne_zero (l : ℕ) (G : WeldedInstance n) (H : AbsForest n)
    (s : Fin H.k) (hsize : (H.comp s).card ≠ 1) (φ₀ : Fin H.k → Label n)
    (hμ : H.muComp l G s φ₀ ≠ 0) : componentScale l G H s ≠ 0 := by
  rw [muComp_eq_scale_forestWeight l G H s hsize φ₀] at hμ
  exact (mul_ne_zero_iff.mp hμ).1

/-- Conditioning the reference component measure cancels its global
normalizer. The resulting finite law is precisely the conditioned supported
edge-product law. -/
theorem muComp_condition_eq_forestWeight (l : ℕ) (G : WeldedInstance n) (H : AbsForest n)
    (s : Fin H.k) (hsize : (H.comp s).card ≠ 1) (φ₀ : Fin H.k → Label n)
    (hμ : H.muComp l G s φ₀ ≠ 0) (T : (Fin H.k → Label n) → Prop)
    [DecidablePred T] (φ : Fin H.k → Label n) :
    (if T φ then H.muComp l G s φ else 0) /
      (∑ ψ, if T ψ then H.muComp l G s ψ else 0) =
    (if T φ then forestWeight (componentEdges H s) (componentKernel l G H)
        (componentAllowed l H s) φ else 0) /
      (∑ ψ, if T ψ then forestWeight (componentEdges H s) (componentKernel l G H)
        (componentAllowed l H s) ψ else 0) := by
  have h (ψ : Fin H.k → Label n) :
      (if T ψ then H.muComp l G s ψ else 0) =
      componentScale l G H s *
        (if T ψ then forestWeight (componentEdges H s) (componentKernel l G H)
          (componentAllowed l H s) ψ else 0) := by
    rw [muComp_eq_scale_forestWeight l G H s hsize ψ]
    split_ifs <;> simp
  simp_rw [h]
  exact normalize_scale (fun ψ => if T ψ then
    forestWeight (componentEdges H s) (componentKernel l G H) (componentAllowed l H s) ψ else 0)
    _ (componentScale_ne_zero l G H s hsize φ₀ hμ) φ

theorem componentEdges_ordered (H : AbsForest n) (hH : H.IsValid) (s : Fin H.k) :
    ∀ p ∈ componentEdges H s, p.1 < p.2 := by
  classical
  intro p hp
  exact hH.1 p (Finset.mem_filter.mp hp).1

theorem componentEdges_acyclic (H : AbsForest n) (hH : H.IsValid) (s : Fin H.k) :
    (edgeGraph (componentEdges H s)).IsAcyclic := by
  apply hH.2.1.anti
  intro u v h
  rcases h with ⟨hne, h | h⟩
  · exact ⟨hne, Or.inl (Finset.mem_filter.mp h).1⟩
  · exact ⟨hne, Or.inr (Finset.mem_filter.mp h).1⟩

theorem component_card_ne_one_of_edge (H : AbsForest n) (hH : H.IsValid) (s : Fin H.k)
    (e : Fin H.k × Fin H.k) (he : e ∈ componentEdges H s) : (H.comp s).card ≠ 1 := by
  classical
  obtain ⟨heE, he₁⟩ := Finset.mem_filter.mp he
  have hr : H.graph.Reachable e.1 e.2 :=
    SimpleGraph.Adj.reachable ⟨ne_of_lt (hH.1 e heE), Or.inl heE⟩
  have he₂ : e.2 ∈ H.comp s := by
    simp only [AbsForest.comp, Finset.mem_filter, Finset.mem_univ, true_and] at he₁ ⊢
    exact he₁.trans hr
  intro hsize
  exact (ne_of_lt (hH.1 e heE)) ((Finset.card_le_one.mp hsize.le) e.1 he₁ e.2 he₂)

def componentCut (H : AbsForest n) (s : Fin H.k) (e : Fin H.k × Fin H.k)
    (u : Fin H.k) : Prop := (edgeGraph ((componentEdges H s).erase e)).Reachable e.1 u

/-- Every forest edge supplies a genuine separator for the factorization
theorems, with no additional graph assumption left to discharge. -/
theorem componentCut_spec (H : AbsForest n) (hH : H.IsValid) (s : Fin H.k)
    (e : Fin H.k × Fin H.k) (he : e ∈ componentEdges H s) :
    componentCut H s e e.1 ∧ ¬componentCut H s e e.2 ∧
      ∀ p ∈ (componentEdges H s).erase e,
        componentCut H s e p.1 ↔ componentCut H s e p.2 := by
  refine ⟨SimpleGraph.Reachable.refl _, ?_, ?_⟩
  · exact forest_cut_not_reachable _ _ (componentEdges_ordered H hH s)
      (componentEdges_acyclic H hH s) he
  · exact forest_cut_closed _ _ (componentEdges_ordered H hH s)

/-- Unnormalized branch factorization of the actual canonical `muComp`.
Together with `muComp_condition_eq_forestWeight` and
`supported_tree_bridge_conditional_factor`, this gives its exact normalized
endpoint-conditioned independence law. -/
theorem muComp_bridge_factor (l : ℕ) (G : WeldedInstance n) (H : AbsForest n)
    (hH : H.IsValid) (s : Fin H.k) (e : Fin H.k × Fin H.k)
    (he : e ∈ componentEdges H s) (φ : Fin H.k → Label n) :
    let P := componentCut H s e
    letI : DecidablePred P := Classical.decPred P
    H.muComp l G s φ = componentScale l G H s *
      (supportedBranchWeight ((componentEdges H s).erase e) P
        (componentKernel l G H) (componentAllowed l H s) (fun v => φ v) *
      supportedBranchWeight ((componentEdges H s).erase e) (fun v => ¬P v)
        (componentKernel l G H) (componentAllowed l H s) (fun v => φ v) *
      kappa l G (H.color e) (φ e.1).val (φ e.2).val) := by
  classical
  dsimp only
  rw [muComp_eq_scale_forestWeight l G H s (component_card_ne_one_of_edge H hH s e he) φ]
  congr 1
  exact forestWeight_bridge_branches _ _ _ _ _ _ he (componentCut_spec H hH s e he).2.2

end WeldedPath.Supplement.ForestFactorization

end

-- Solutions.WeldedPathReferenceProduct
section

namespace WeldedPath.Supplement.ForestFactorization

open scoped BigOperators
open FiniteWeightedForest
open Classical

variable {n : ℕ}

noncomputable def compRoot (H : AbsForest n) (u : Fin H.k) : Fin H.k :=
  (H.comp u).min' ⟨u, by simp [AbsForest.comp]⟩

lemma compRoot_reachable (H : AbsForest n) (u : Fin H.k) :
    H.graph.Reachable (compRoot H u) u := by
  have h := Finset.min'_mem (H.comp u) ⟨u, by simp [AbsForest.comp]⟩
  exact ((Finset.mem_filter.mp h).2).symm

lemma compRoot_isRoot (H : AbsForest n) (u : Fin H.k) : H.IsCompRoot (compRoot H u) := by
  intro v hv
  exact Finset.min'_le _ _ (Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, (compRoot_reachable H u).symm.trans hv⟩)

lemma mem_comp_iff_root_eq (H : AbsForest n) (s u : Fin H.k) (hs : H.IsCompRoot s) :
    u ∈ H.comp s ↔ compRoot H u = s := by
  classical
  constructor
  · intro hu
    have hsu := (Finset.mem_filter.mp hu).2
    have hru := compRoot_reachable H u
    exact le_antisymm ((compRoot_isRoot H u) s (hru.trans hsu.symm))
      (hs _ (hsu.trans hru.symm))
  · intro heq
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, heq ▸ compRoot_reachable H u⟩

/-- Component edge products partition the full stored-edge product exactly. -/
theorem prod_component_edgeWeight (H : AbsForest n)
    (K : (Fin H.k × Fin H.k) → Label n → Label n → ℝ) (φ : Fin H.k → Label n) :
    (∏ s ∈ Finset.univ.filter H.IsCompRoot, edgeWeight (componentEdges H s) K φ) =
      edgeWeight H.E K φ := by
  classical
  calc
    _ = ∏ s ∈ Finset.univ.filter H.IsCompRoot,
        ∏ p ∈ H.E.filter (fun p => compRoot H p.1 = s), K p (φ p.1) (φ p.2) := by
      apply Finset.prod_congr rfl
      intro s hs
      have hsroot := (Finset.mem_filter.mp hs).2
      unfold edgeWeight componentEdges
      congr 1
      exact Finset.filter_congr (fun p _ => mem_comp_iff_root_eq H s p.1 hsroot)
    _ = _ := Finset.prod_fiberwise_of_maps_to
      (fun p _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, compRoot_isRoot H p.1⟩)
      (fun p => K p (φ p.1) (φ p.2))

noncomputable def referenceScale (l : ℕ) (G : WeldedInstance n) (H : AbsForest n) : ℝ := by
  classical
  exact ∏ s ∈ Finset.univ.filter H.IsCompRoot,
    if (H.comp s).card = 1 then 1 / (labelBound n : ℝ) else componentScale l G H s

def referenceAllowed (l : ℕ) (H : AbsForest n) (u : Fin H.k) (x : Label n) : Prop :=
  (H.IsCompRoot u → (H.comp u).card = 1 → 1 ≤ x.val) ∧
  (∀ s, H.IsCompRoot s → (H.comp s).card ≠ 1 → u ∈ H.comp s →
    x.val ∈ Vmid n l ∪ Vbd n l)

noncomputable def componentCondition (l : ℕ) (H : AbsForest n) (s : Fin H.k)
    (φ : Fin H.k → Label n) : Prop := by
  classical
  exact if (H.comp s).card = 1 then 1 ≤ (φ s).val else
    ∀ u ∈ H.comp s, (φ u).val ∈ Vmid n l ∪ Vbd n l

lemma muComp_eq_componentCondition (l : ℕ) (G : WeldedInstance n) (H : AbsForest n)
    (hH : H.IsValid) (s : Fin H.k) (φ : Fin H.k → Label n) :
    H.muComp l G s φ =
      (if (H.comp s).card = 1 then 1 / (labelBound n : ℝ) else componentScale l G H s) *
      (if componentCondition l H s φ then
        edgeWeight (componentEdges H s) (componentKernel l G H) φ else 0) := by
  classical
  by_cases hs : (H.comp s).card = 1
  · have hE : componentEdges H s = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro e he
      exact component_card_ne_one_of_edge H hH s e he hs
    simp [AbsForest.muComp, hs, componentCondition, hE, edgeWeight]
  · rw [muComp_eq_scale_forestWeight l G H s hs φ]
    simp only [hs, ite_false, componentCondition, forestWeight, componentAllowed]
    split_ifs <;> simp_all

lemma componentConditions_iff (l : ℕ) (H : AbsForest n) (φ : Fin H.k → Label n) :
    (∀ s ∈ Finset.univ.filter H.IsCompRoot, componentCondition l H s φ) ↔
      ∀ u, referenceAllowed l H u (φ u) := by
  classical
  constructor
  · intro h u
    constructor
    · intro hu hs
      have hsu := h u (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩)
      simpa [componentCondition, hs] using hsu
    · intro s hs hsize hu
      have hsu := h s (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩)
      have hsu' : ∀ u ∈ H.comp s, (φ u).val ∈ Vmid n l ∪ Vbd n l := by
        simpa [componentCondition, hsize] using hsu
      exact hsu' u hu
  · intro h s hs
    have hsroot := (Finset.mem_filter.mp hs).2
    by_cases hsize : (H.comp s).card = 1
    · simpa [componentCondition, hsize] using (h s).1 hsroot hsize
    · simp only [componentCondition, hsize, ite_false]
      intro u hu
      exact (h u).2 s hsroot hsize hu

/-- The actual canonical reference law is one assignment-independent
constant times the full forest edge product and unary support constraints.
This includes singleton components and zero normalizers. -/
theorem muRef_eq_scale_forestWeight (l : ℕ) (G : WeldedInstance n) (H : AbsForest n)
    (hH : H.IsValid) (φ : Fin H.k → Label n) :
    H.muRef l G φ = referenceScale l G H *
      forestWeight H.E (componentKernel l G H) (referenceAllowed l H) φ := by
  classical
  unfold AbsForest.muRef
  simp_rw [muComp_eq_componentCondition l G H hH]
  rw [Finset.prod_mul_distrib]
  change referenceScale l G H * _ = referenceScale l G H * _
  congr 1
  rw [Finset.prod_ite_zero, prod_component_edgeWeight]
  simp only [forestWeight, componentConditions_iff]
  split_ifs <;> rfl

theorem referenceScale_ne_zero (l : ℕ) (G : WeldedInstance n) (H : AbsForest n)
    (hH : H.IsValid) (φ₀ : Fin H.k → Label n) (hμ : H.muRef l G φ₀ ≠ 0) :
    referenceScale l G H ≠ 0 := by
  rw [muRef_eq_scale_forestWeight l G H hH φ₀] at hμ
  exact (mul_ne_zero_iff.mp hμ).1

/-- Any conditioning event cancels the reference normalizer. This leaves
only the local graph weight for the subsequent stochastic-process analysis. -/
theorem muRef_condition_eq_forestWeight (l : ℕ) (G : WeldedInstance n) (H : AbsForest n)
    (hH : H.IsValid) (φ₀ : Fin H.k → Label n) (hμ : H.muRef l G φ₀ ≠ 0)
    (T : (Fin H.k → Label n) → Prop) [DecidablePred T] (φ : Fin H.k → Label n) :
    (if T φ then H.muRef l G φ else 0) /
      (∑ ψ, if T ψ then H.muRef l G ψ else 0) =
    (if T φ then forestWeight H.E (componentKernel l G H) (referenceAllowed l H) φ else 0) /
      (∑ ψ, if T ψ then forestWeight H.E (componentKernel l G H) (referenceAllowed l H) ψ else 0) := by
  have h (ψ : Fin H.k → Label n) :
      (if T ψ then H.muRef l G ψ else 0) = referenceScale l G H *
        (if T ψ then forestWeight H.E (componentKernel l G H) (referenceAllowed l H) ψ else 0) := by
    rw [muRef_eq_scale_forestWeight l G H hH ψ]
    split_ifs <;> simp
  simp_rw [h]
  exact normalize_scale (fun ψ => if T ψ then
    forestWeight H.E (componentKernel l G H) (referenceAllowed l H) ψ else 0)
    _ (referenceScale_ne_zero l G H hH φ₀ hμ) φ

end WeldedPath.Supplement.ForestFactorization

end

-- Solutions.WeldedPathComponentRestriction
section

namespace WeldedPath.Supplement.ComponentRestriction

open Classical FixedData ForestOrder ForestFactorization FiniteWeightedForest
open scoped BigOperators

variable {n : ℕ}

lemma root_mem_comp (H : AbsForest n) (s : Fin H.k) : s ∈ H.comp s :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ _, SimpleGraph.Reachable.refl _⟩

lemma edge_endpoints_in_comp (H : AbsForest n) (hH : H.IsValid) (s : Fin H.k)
    (e : Fin H.k × Fin H.k) (he : e ∈ componentEdges H s) :
    e.1 ∈ H.comp s ∧ e.2 ∈ H.comp s := by
  have hh := Finset.mem_filter.mp he
  refine ⟨hh.2, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
  have hadj : H.graph.Adj e.1 e.2 := ⟨ne_of_lt (hH.1 e hh.1), Or.inl hh.1⟩
  exact (Finset.mem_filter.mp hh.2).2.trans hadj.reachable

theorem wfix_depends_only_on_component (H : AbsForest n) (hH : H.IsValid)
    (s : Fin H.k) (φ ψ : Fin H.k → Label n)
    (hφ : ∀ u ∈ H.comp s, φ u = ψ u) : H.Wfix φ s = H.Wfix ψ s := by
  apply (wfix_eq_iff_agree_sfix H hH φ ψ s).mpr
  intro u hu
  exact hφ u (sfix_subset_comp H hH ψ s hu)

theorem ctree_depends_only_on_component (H : AbsForest n) (hH : H.IsValid)
    (s : Fin H.k) (φ ψ : Fin H.k → Label n)
    (hφ : ∀ u ∈ H.comp s, φ u = ψ u) : H.Ctree φ s = H.Ctree ψ s :=
  congrArg Prod.fst (wfix_depends_only_on_component H hH s φ ψ hφ)

theorem component_edgeWeight_congr (l : ℕ) (G : WeldedInstance n)
    (H : AbsForest n) (hH : H.IsValid) (s : Fin H.k)
    (φ ψ : Fin H.k → Label n) (hφ : ∀ u ∈ H.comp s, φ u = ψ u) :
    edgeWeight (componentEdges H s) (componentKernel l G H) φ =
      edgeWeight (componentEdges H s) (componentKernel l G H) ψ := by
  apply Finset.prod_congr rfl
  intro e he
  have hh := edge_endpoints_in_comp H hH s e he
  exact congrArg₂ (componentKernel l G H e) (hφ e.1 hh.1) (hφ e.2 hh.2)

theorem componentCondition_congr (l : ℕ) (H : AbsForest n) (s : Fin H.k)
    (φ ψ : Fin H.k → Label n) (hφ : ∀ u ∈ H.comp s, φ u = ψ u) :
    componentCondition l H s φ ↔ componentCondition l H s ψ := by
  unfold componentCondition
  split_ifs
  · rw [hφ s (root_mem_comp H s)]
  · constructor
    · intro h u hu
      rw [← hφ u hu]
      exact h u hu
    · intro h u hu
      rw [hφ u hu]
      exact h u hu

theorem muComp_depends_only_on_component (l : ℕ) (G : WeldedInstance n)
    (H : AbsForest n) (hH : H.IsValid) (s : Fin H.k)
    (φ ψ : Fin H.k → Label n) (hφ : ∀ u ∈ H.comp s, φ u = ψ u) :
    H.muComp l G s φ = H.muComp l G s ψ := by
  rw [muComp_eq_componentCondition l G H hH s φ,
    muComp_eq_componentCondition l G H hH s ψ,
    component_edgeWeight_congr l G H hH s φ ψ hφ,
    propext (componentCondition_congr l H s φ ψ hφ)]

noncomputable def extendComponent (H : AbsForest n) (s : Fin H.k)
    (z : H.comp s → Label n) (u : Fin H.k) : Label n :=
  if hu : u ∈ H.comp s then z ⟨u, hu⟩ else 0

@[simp] theorem extendComponent_on (H : AbsForest n) (s : Fin H.k)
    (z : H.comp s → Label n) (u : H.comp s) : extendComponent H s z u = z u := by
  simp only [extendComponent, dif_pos u.property]

noncomputable def componentWeight (l : ℕ) (G : WeldedInstance n)
    (H : AbsForest n) (s : Fin H.k) (z : H.comp s → Label n) : ℝ :=
  H.muComp l G s (extendComponent H s z)

theorem muComp_restrict (l : ℕ) (G : WeldedInstance n) (H : AbsForest n)
    (hH : H.IsValid) (s : Fin H.k) (φ : Fin H.k → Label n) :
    H.muComp l G s φ = componentWeight l G H s (fun u => φ u.val) := by
  apply muComp_depends_only_on_component l G H hH s
  intro u hu
  simp only [extendComponent, dif_pos hu]

/-- The full reference law is literally a product of weights on independent
component coordinate sets. No extension labels enter a component factor. -/
theorem muRef_eq_component_product (l : ℕ) (G : WeldedInstance n)
    (H : AbsForest n) (hH : H.IsValid) (φ : Fin H.k → Label n) :
    H.muRef l G φ = ∏ s ∈ Finset.univ.filter H.IsCompRoot,
      componentWeight l G H s (fun u => φ u.val) := by
  apply Finset.prod_congr rfl
  intro s _
  exact muComp_restrict l G H hH s φ

end WeldedPath.Supplement.ComponentRestriction

end

-- Solutions.WeldedPathComponentForest
section

namespace WeldedPath.Supplement.ComponentForest

open Classical ComponentRestriction

variable {n : ℕ}

noncomputable def vertexEquiv (H : AbsForest n) (s : Fin H.k) :
    Fin (H.comp s).card ≃o H.comp s := (H.comp s).orderIsoOfFin rfl

noncomputable def vertexMap (H : AbsForest n) (s : Fin H.k)
    (i : Fin (H.comp s).card) : Fin H.k := (vertexEquiv H s i).val

lemma vertexMap_mem (H : AbsForest n) (s : Fin H.k) (i : Fin (H.comp s).card) :
    vertexMap H s i ∈ H.comp s := (vertexEquiv H s i).property

lemma vertexMap_injective (H : AbsForest n) (s : Fin H.k) :
    Function.Injective (vertexMap H s) := by
  intro i j hij
  apply (vertexEquiv H s).injective
  exact Subtype.ext hij

lemma vertexMap_lt_iff (H : AbsForest n) (s : Fin H.k)
    (i j : Fin (H.comp s).card) : vertexMap H s i < vertexMap H s j ↔ i < j :=
  (vertexEquiv H s).lt_iff_lt

noncomputable def edgeMap (H : AbsForest n) (s : Fin H.k)
    (p : Fin (H.comp s).card × Fin (H.comp s).card) : Fin H.k × Fin H.k :=
  (vertexMap H s p.1, vertexMap H s p.2)

lemma edgeMap_injective (H : AbsForest n) (s : Fin H.k) :
    Function.Injective (edgeMap H s) := by
  intro p q hpq
  exact Prod.ext (vertexMap_injective H s (congrArg Prod.fst hpq))
    (vertexMap_injective H s (congrArg Prod.snd hpq))

noncomputable abbrev componentForest (H : AbsForest n) (s : Fin H.k) : AbsForest n where
  k := (H.comp s).card
  E := Finset.univ.filter (fun p => edgeMap H s p ∈ H.E)
  color p := H.color (edgeMap H s p)
  lab i := H.lab (vertexMap H s i)

@[simp] lemma mem_edges (H : AbsForest n) (s : Fin H.k)
    (p : Fin (H.comp s).card × Fin (H.comp s).card) :
    p ∈ (componentForest H s).E ↔ edgeMap H s p ∈ H.E := by
  change p ∈ (Finset.univ.filter (fun q => edgeMap H s q ∈ H.E)) ↔ _
  exact ⟨fun hp => (Finset.mem_filter.mp hp).2,
    fun hp => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩⟩

lemma graph_adj_iff (H : AbsForest n) (s : Fin H.k) (i j : Fin (H.comp s).card) :
    (componentForest H s).graph.Adj i j ↔ H.graph.Adj (vertexMap H s i) (vertexMap H s j) := by
  constructor
  · rintro ⟨hne, he | he⟩
    · exact ⟨fun h => hne (vertexMap_injective H s h), Or.inl ((mem_edges H s _).mp he)⟩
    · exact ⟨fun h => hne (vertexMap_injective H s h), Or.inr ((mem_edges H s _).mp he)⟩
  · rintro ⟨hne, he | he⟩
    · exact ⟨fun h => hne (congrArg (vertexMap H s) h), Or.inl ((mem_edges H s _).mpr he)⟩
    · exact ⟨fun h => hne (congrArg (vertexMap H s) h), Or.inr ((mem_edges H s _).mpr he)⟩

noncomputable def graphEmbedding (H : AbsForest n) (s : Fin H.k) :
    (componentForest H s).graph ↪g H.graph where
  toFun := vertexMap H s
  inj' := vertexMap_injective H s
  map_rel_iff' := (graph_adj_iff H s _ _).symm

noncomputable def graphIsoInduce (H : AbsForest n) (s : Fin H.k) :
    (componentForest H s).graph ≃g H.graph.induce (↑(H.comp s) : Set (Fin H.k)) where
  __ := (vertexEquiv H s).toEquiv
  map_rel_iff' := (graph_adj_iff H s _ _).symm

theorem component_connected (H : AbsForest n) (s : Fin H.k)
    (i j : Fin (H.comp s).card) : (componentForest H s).graph.Reachable i j := by
  have hi := (Finset.mem_filter.mp (vertexMap_mem H s i)).2
  have hj := (Finset.mem_filter.mp (vertexMap_mem H s j)).2
  obtain ⟨p⟩ := hi.symm.trans hj
  have hp : ∀ x ∈ p.support, x ∈ H.comp s := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi.trans (p.takeUntil x hx).reachable⟩
  have hreach := (p.induce (↑(H.comp s) : Set (Fin H.k)) hp).reachable
  have hm := hreach.map (graphIsoInduce H s).symm.toHom
  change (componentForest H s).graph.Reachable
    ((vertexEquiv H s).symm (vertexEquiv H s i))
    ((vertexEquiv H s).symm (vertexEquiv H s j)) at hm
  simpa only [OrderIso.symm_apply_apply] using hm

theorem component_valid (H : AbsForest n) (hH : H.IsValid) (s : Fin H.k) :
    (componentForest H s).IsValid := by
  refine ⟨?_, hH.2.1.embedding (graphEmbedding H s), ?_, ?_, ?_⟩
  · intro p hp
    exact (vertexMap_lt_iff H s p.1 p.2).mp (hH.1 _ ((mem_edges H s p).mp hp))
  · intro p hp q hq hpq hi
    apply hH.2.2.1 (edgeMap H s p) ((mem_edges H s p).mp hp)
      (edgeMap H s q) ((mem_edges H s q).mp hq)
      (fun heq => hpq (edgeMap_injective H s heq))
    rcases hi with hi | hi | hi | hi
    · exact Or.inl (congrArg (vertexMap H s) hi)
    · exact Or.inr (Or.inl (congrArg (vertexMap H s) hi))
    · exact Or.inr (Or.inr (Or.inl (congrArg (vertexMap H s) hi)))
    · exact Or.inr (Or.inr (Or.inr (congrArg (vertexMap H s) hi)))
  · intro i j x hi hj
    exact vertexMap_injective H s (hH.2.2.2.1 _ _ x hi hj)
  · intro i
    rcases hH.2.2.2.2 (vertexMap H s i) with hl | ⟨p, hp, hi⟩
    · exact Or.inl hl
    · have hadj : H.graph.Adj p.1 p.2 := ⟨ne_of_lt (hH.1 p hp), Or.inl hp⟩
      have hh : p.1 ∈ H.comp s ∧ p.2 ∈ H.comp s := by
        rcases hi with hi | hi
        · have h₁ : p.1 ∈ H.comp s := hi.symm ▸ vertexMap_mem H s i
          exact ⟨h₁, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            (Finset.mem_filter.mp h₁).2.trans hadj.reachable⟩⟩
        · have h₂ : p.2 ∈ H.comp s := hi.symm ▸ vertexMap_mem H s i
          exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            (Finset.mem_filter.mp h₂).2.trans hadj.symm.reachable⟩, h₂⟩
      let q : Fin (H.comp s).card × Fin (H.comp s).card :=
        ((vertexEquiv H s).symm ⟨p.1, hh.1⟩, (vertexEquiv H s).symm ⟨p.2, hh.2⟩)
      have heq : edgeMap H s q = p := by simp only [edgeMap, vertexMap, q, OrderIso.apply_symm_apply]
      refine Or.inr ⟨q, (mem_edges H s q).mpr (heq.symm ▸ hp), ?_⟩
      rcases hi with hi | hi
      · exact Or.inl (vertexMap_injective H s ((congrArg Prod.fst heq).trans hi))
      · exact Or.inr (vertexMap_injective H s ((congrArg Prod.snd heq).trans hi))

end WeldedPath.Supplement.ComponentForest

end

-- Solutions.WeldedPathGraphDepth
section

namespace WeldedPath.LoopProof

lemma pow_root_ge_two (n : ℕ) : 2 ≤ 2 ^ (n + 1) := by
  have h := Nat.two_pow_pos n
  rw [pow_succ]
  omega

lemma numV_eq (n : ℕ) : numV n = 2 * (2 ^ (n + 1) - 1) := by
  have h := pow_root_ge_two n
  unfold numV
  rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
  omega

lemma col_zero (n : ℕ) : col n 0 = 0 := by
  have h := pow_root_ge_two n
  simp [col, show 0 < 2 ^ (n + 1) - 1 by omega]

lemma col_exit (n : ℕ) : col n (exitIdx n) = 2 * n + 1 := by
  simp [col, exitIdx]

lemma log_left_le (n v : ℕ) (hv : v < 2 ^ (n + 1) - 1) :
    Nat.log 2 (v + 1) ≤ n := by
  have h : v + 1 < 2 ^ (n + 1) := by omega
  have := (Nat.log_lt_iff_lt_pow (by decide : 1 < 2) (by omega : v + 1 ≠ 0)).2 h
  omega

lemma log_right_le (n v : ℕ) (hv : IsVertex n v) (hr : 2 ^ (n + 1) - 1 ≤ v) :
    Nat.log 2 (v - (2 ^ (n + 1) - 1) + 1) ≤ n := by
  have hn := pow_root_ge_two n
  rw [IsVertex, numV_eq] at hv
  have h : v - (2 ^ (n + 1) - 1) + 1 < 2 ^ (n + 1) := by omega
  have := (Nat.log_lt_iff_lt_pow (by decide : 1 < 2)
    (by omega : v - (2 ^ (n + 1) - 1) + 1 ≠ 0)).2 h
  omega

lemma col_left_le (n v : ℕ) (hv : v < 2 ^ (n + 1) - 1) : col n v ≤ n := by
  simpa [col, hv] using log_left_le n v hv

lemma col_right_ge (n v : ℕ) (hv : IsVertex n v) (hr : 2 ^ (n + 1) - 1 ≤ v) :
    n + 1 ≤ col n v := by
  have hd := log_right_le n v hv hr
  simp only [col, if_neg (by omega : ¬ v < 2 ^ (n + 1) - 1)]
  omega

lemma col_bounds (n v : ℕ) (hv : IsVertex n v) : col n v ≤ 2 * n + 1 := by
  by_cases h : v < 2 ^ (n + 1) - 1
  · have := col_left_le n v h
    omega
  · simp only [col, if_neg h]
    omega

lemma parent_spec {n v p : ℕ} (hp : parent n v = some p) :
    IsVertex n v ∧ IsVertex n p ∧
      ((col n p + 1 = col n v ∧ col n v ≤ n) ∨
        (col n v + 1 = col n p ∧ n + 1 ≤ col n v)) := by
  have hb := pow_root_ge_two n
  unfold parent at hp
  split at hp
  next h =>
    have hv := h.1
    have hvleft : v < 2 ^ (n + 1) - 1 := by
      by_contra hh
      have := col_right_ge n v hv (by omega)
      omega
    have hvpos : 1 ≤ v := by
      by_contra hh
      have heq : v = 0 := by omega
      subst v
      simp [col_zero] at h
    have hpval : p = (v - 1) / 2 := by simpa using hp.symm
    have hpv : p < v := by omega
    have hpV : IsVertex n p := by unfold IsVertex at *; omega
    have hpleft : p < 2 ^ (n + 1) - 1 := by omega
    have hdiv : p + 1 = (v + 1) / 2 := by omega
    have hlog : Nat.log 2 (p + 1) = Nat.log 2 (v + 1) - 1 := by
      rw [hdiv, Nat.log_div_base]
    have hcols : col n p + 1 = col n v := by
      simp only [col, if_pos hvleft] at h
      simp only [col, if_pos hpleft, if_pos hvleft]
      omega
    exact ⟨hv, hpV, Or.inl ⟨hcols, h.2.2⟩⟩
  next h =>
    split at hp
    next h' =>
      have hv := h'.1
      have hvright : 2 ^ (n + 1) - 1 ≤ v := by
        by_contra hh
        have := col_left_le n v (by omega)
        omega
      have hvroot : v ≠ 2 ^ (n + 1) - 1 := by
        intro heq
        have hc : col n v = 2 * n + 1 := by
          simpa [heq, exitIdx] using col_exit n
        omega
      have hvbig : 2 ^ (n + 1) ≤ v := by omega
      have hpval : p = (v - 2 ^ (n + 1)) / 2 + 2 ^ (n + 1) - 1 := by
        simpa using hp.symm
      have hpv : p < v := by omega
      have hpV : IsVertex n p := by unfold IsVertex at *; omega
      have hpright : 2 ^ (n + 1) - 1 ≤ p := by omega
      have hdiv : p - (2 ^ (n + 1) - 1) + 1 =
          (v - (2 ^ (n + 1) - 1) + 1) / 2 := by omega
      have hlog : Nat.log 2 (p - (2 ^ (n + 1) - 1) + 1) =
          Nat.log 2 (v - (2 ^ (n + 1) - 1) + 1) - 1 := by
        rw [hdiv, Nat.log_div_base]
      have hd := log_right_le n v hv hvright
      have hdpos : 1 ≤ Nat.log 2 (v - (2 ^ (n + 1) - 1) + 1) := by
        have := Nat.log_pos (by decide : 1 < 2)
          (show 2 ≤ v - (2 ^ (n + 1) - 1) + 1 by omega)
        omega
      have hcols : col n v + 1 = col n p := by
        simp only [col, if_neg (by omega : ¬ v < 2 ^ (n + 1) - 1),
          if_neg (by omega : ¬ p < 2 ^ (n + 1) - 1)]
        omega
      exact ⟨hv, hpV, Or.inr ⟨hcols, h'.2.1⟩⟩
    next h' => simp at hp

lemma parent_eq_exit_imp {n v : ℕ} (hp : parent n v = some (exitIdx n)) :
    v = 2 ^ (n + 1) ∨ v = 2 ^ (n + 1) + 1 := by
  have hs := parent_spec hp
  have hc := col_exit n
  have hb := pow_root_ge_two n
  unfold parent at hp
  split at hp
  next h =>
    rcases hs.2.2 with hleft | hright <;> omega
  next h =>
    split at hp
    next h' =>
      have hvright : 2 ^ (n + 1) - 1 ≤ v := by
        by_contra hh
        have := col_left_le n v (by omega)
        omega
      have hvroot : v ≠ 2 ^ (n + 1) - 1 := by
        intro heq
        have hc' : col n v = 2 * n + 1 := by simpa [heq, exitIdx] using col_exit n
        omega
      simp only [Option.some.injEq, exitIdx] at hp
      omega
    next h' => simp at hp

lemma tree_mem_iff {n : ℕ} {G : WeldedInstance n} {v : ℕ} :
    Edge.tree v ∈ G.edges ↔ IsVertex n v ∧ (parent n v).isSome := by
  simp [WeldedInstance.edges, WeldedInstance.treeEdges, WeldedInstance.weldEdges, IsVertex]

lemma weld_mem_iff {n : ℕ} {G : WeldedInstance n} {u w : ℕ} :
    Edge.weld u w ∈ G.edges ↔ (u, w) ∈ G.weld := by
  simp [WeldedInstance.edges, WeldedInstance.treeEdges, WeldedInstance.weldEdges]

lemma edge_endpoints {n : ℕ} {G : WeldedInstance n} (hG : G.IsValid)
    {e : Edge} (he : e ∈ G.edges) :
    IsVertex n e.tail ∧ IsVertex n (e.head n) ∧
      (col n e.tail + 1 = col n (e.head n) ∨ col n (e.head n) + 1 = col n e.tail) := by
  cases e with
  | tree v =>
    have hv := tree_mem_iff.mp he
    cases hp : parent n v with
    | none => simp [hp] at hv
    | some p =>
      have hs := parent_spec hp
      simp only [Edge.tail, Edge.head, hp, Option.getD_some]
      exact ⟨hs.1, hs.2.1, hs.2.2.elim (fun h => Or.inr h.1) (fun h => Or.inl h.1)⟩
  | weld u w =>
    have hw := hG.1.1 (u, w) (weld_mem_iff.mp he)
    dsimp only at hw
    simp only [Edge.tail, Edge.head]
    exact ⟨hw.1, hw.2.2.1, Or.inl (by omega)⟩

lemma tree_head_col {n : ℕ} {G : WeldedInstance n} {v : ℕ}
    (he : Edge.tree v ∈ G.edges) :
    col n ((Edge.tree v).head n) = if col n v ≤ n then col n v - 1 else col n v + 1 := by
  have hv := tree_mem_iff.mp he
  cases hp : parent n v with
  | none => simp [hp] at hv
  | some p =>
    have hs := (parent_spec hp).2.2
    simp only [Edge.head, hp, Option.getD_some]
    rcases hs with h | h
    · rw [if_pos h.2]
      omega
    · rw [if_neg (by omega : ¬ col n v ≤ n)]
      omega

lemma same_class_cols {n l : ℕ} {G : WeldedInstance n} (hG : G.IsValid)
    {e e' : Edge} (he : e ∈ G.edges) (he' : e' ∈ G.edges)
    (hclass : G.bEdge l e = G.bEdge l e') (hnone : G.bEdge l e ≠ none) :
    col n e.tail = col n e'.tail ∧ col n (e.head n) = col n (e'.head n) := by
  cases e with
  | tree v =>
    have hv : n - l ≤ col n v ∧ col n v ≤ n + l := by
      by_contra h
      simp only [WeldedInstance.bEdge, if_neg h, ne_eq, not_true_eq_false] at hnone
    cases e' with
    | tree w =>
      have hw : n - l ≤ col n w ∧ col n w ≤ n + l := by
        by_contra h
        simp only [WeldedInstance.bEdge, if_pos hv, if_neg h, reduceCtorEq] at hclass
      have hc : col n v = col n w := by
        have hboth : col n v = col n w ∧ G.color (.tree v) = G.color (.tree w) := by
          simpa only [WeldedInstance.bEdge, if_pos hv, if_pos hw,
            Option.some.injEq, EdgeClass.tr.injEq] using hclass
        exact hboth.1
      refine ⟨hc, ?_⟩
      rw [tree_head_col he, tree_head_col he', hc]
    | weld u w => simp [WeldedInstance.bEdge, hv] at hclass
  | weld u w =>
    cases e' with
    | tree v =>
      simp only [WeldedInstance.bEdge] at hclass
      split at hclass <;> simp_all
    | weld u' w' =>
      have hw := hG.1.1 (u, w) (weld_mem_iff.mp he)
      have hw' := hG.1.1 (u', w') (weld_mem_iff.mp he')
      dsimp only at hw hw'
      simp only [Edge.tail, Edge.head]
      exact ⟨by omega, by omega⟩

end WeldedPath.LoopProof

end

-- Solutions.WeldedPathCrossingExclusion
section

namespace WeldedPath.Supplement.CrossingExclusion

open WeldedInstance InjDb
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}

lemma reachable_preserves {X : Type*} {J : SimpleGraph X} (P : X → Prop)
    (h : ∀ u v, J.Adj u v → (P u ↔ P v)) {u v : X} (hr : J.Reachable u v) :
    P u ↔ P v := by
  obtain ⟨w⟩ := hr
  induction w with
  | nil => rfl
  | cons huv _ ih => exact (h _ _ huv).trans ih

lemma edge_adj (H : AbsForest n) (hH : H.IsValid) {p : Fin H.k × Fin H.k}
    (hp : p ∈ H.E) : H.graph.Adj p.1 p.2 := by
  exact ⟨ne_of_lt (hH.1 p hp), Or.inl hp⟩

lemma comp_root_exists (H : AbsForest n) (u : Fin H.k) :
    ∃ s, H.IsCompRoot s ∧ H.graph.Reachable s u := by
  classical
  have hu : u ∈ H.comp u := by simp [AbsForest.comp]
  let s := (H.comp u).min' ⟨u, hu⟩
  have hs : H.graph.Reachable u s := (Finset.mem_filter.mp
    (Finset.min'_mem (H.comp u) ⟨u, hu⟩)).2
  refine ⟨s, ?_, hs.symm⟩
  intro v hv
  exact Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs.trans hv⟩)

lemma edge_kappa_ne_zero (H : AbsForest n) (hH : H.IsValid)
    (ϕ : Fin H.k → Label n) (hmu : H.muRef l G ϕ ≠ 0)
    {p : Fin H.k × Fin H.k} (hp : p ∈ H.E) :
    kappa l G (H.color p) (ϕ p.1).1 (ϕ p.2).1 ≠ 0 := by
  classical
  obtain ⟨s, hs, hsu⟩ := comp_root_exists H p.1
  have hsu' : p.1 ∈ H.comp s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsu⟩
  have hsv : p.2 ∈ H.comp s := Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, hsu.trans (edge_adj H hH hp).reachable⟩
  have hcard : (H.comp s).card ≠ 1 := by
    intro hc
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hc
    have h1 : p.1 = a := by simpa only [ha, Finset.mem_singleton] using hsu'
    have h2 : p.2 = a := by simpa only [ha, Finset.mem_singleton] using hsv
    have heq : p.1 = p.2 := h1.trans h2.symm
    exact (ne_of_lt (hH.1 p hp)) heq
  have hc : H.muComp l G s ϕ ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp hmu) s (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩)
  unfold AbsForest.muComp at hc
  dsimp only at hc
  rw [if_neg hcard] at hc
  split at hc
  · have hw := (mul_ne_zero_iff.mp hc).2
    exact (Finset.prod_ne_zero_iff.mp hw) p (Finset.mem_filter.mpr ⟨hp, hsu'⟩)
  · exact False.elim (hc rfl)

lemma permData_orientation {u : ℕ} {α : Fin 3} {b : PClass n l}
    {e : ↥(G.classEdges l b.1)} {t : Bool}
    (h : permData l G u α = some ⟨b, e, t⟩) :
    (t = true → u = e.1.tail) ∧ (t = false → u = e.1.head n) := by
  classical
  unfold permData at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · cases h
        rename_i e' he' hh
        have hi := (Classical.choose_spec hh.2).2.2
        constructor
        · intro ht
          simpa using ht
        · intro ht
          have hnt : u ≠ e'.tail := by simpa using ht
          exact hi.resolve_left hnt
      · simp at h

lemma class_pair_half (hG : G.IsValid) {e e' : Edge}
    (he : e ∈ G.edges) (he' : e' ∈ G.edges)
    (hc : G.bEdge l e = G.bEdge l e') (hne : G.bEdge l e ≠ none) :
    IsVertex n e.tail ∧ IsVertex n (e'.head n) ∧
      ((col n e.tail ≤ n ↔ col n (e'.head n) ≤ n) ∨
        (e.tail ∈ Vweld n ∧ e'.head n ∈ Vweld n)) := by
  have hends := LoopProof.edge_endpoints hG he
  have hends' := LoopProof.edge_endpoints hG he'
  have hcols := LoopProof.same_class_cols hG he he' hc hne
  refine ⟨hends.1, hends'.2.1, ?_⟩
  cases e with
  | tree v =>
    left
    rw [← hcols.2, LoopProof.tree_head_col he]
    simp only [Edge.tail]
    split <;> omega
  | weld u w =>
    right
    have hw := hG.1.1 (u, w) (LoopProof.weld_mem_iff.mp he)
    constructor
    · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hw.1, Or.inl hw.2.1⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hends'.2.1,
        Or.inr (by simpa only [Edge.head] using hcols.2.symm.trans hw.2.2.2)⟩

lemma kappa_half (hG : G.IsValid) {α : Fin 3} {u v : ℕ}
    (hk : kappa l G α u v ≠ 0) :
    (col n u ≤ n ↔ col n v ≤ n) ∨ (u ∈ Vweld n ∧ v ∈ Vweld n) := by
  classical
  cases hpd : permData l G u α with
  | none => simp [kappa, hpd] at hk
  | some d =>
    obtain ⟨b, e, t⟩ := d
    have hor := permData_orientation hpd
    have hm : (t = true ∧ v ∈ (G.classEdges l b.1).image (fun g => g.head n)) ∨
        (t = false ∧ v ∈ (G.classEdges l b.1).image Edge.tail) := by
      by_contra hh
      exact hk (by simp only [kappa, hpd, if_neg hh])
    have he := Finset.mem_filter.mp e.2
    rcases hm with ⟨ht, hv⟩ | ⟨ht, hv⟩
    · obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp hv
      have he' := Finset.mem_filter.mp he'
      rw [hor.1 ht]
      exact (class_pair_half hG he.1 he'.1 (he.2.trans he'.2.symm)
        (by simp [he.2])).2.2
    · obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp hv
      have he' := Finset.mem_filter.mp he'
      rw [hor.2 ht]
      rcases (class_pair_half hG he'.1 he.1 (he'.2.trans he.2.symm)
        (by simp [he'.2])).2.2 with hh | hh
      · exact Or.inl hh.symm
      · exact Or.inr hh.symm

lemma tree_reachable_half (hG : G.IsValid) (H : AbsForest n) (hH : H.IsValid)
    (ϕ : Fin H.k → Label n) (hmu : H.muRef l G ϕ ≠ 0) {u v : Fin H.k}
    (hr : (H.treeGraph ϕ).Reachable u v) :
    col n (ϕ u).1 ≤ n ↔ col n (ϕ v).1 ≤ n := by
  apply reachable_preserves (fun u => col n (ϕ u).1 ≤ n) _ hr
  intro a b hab
  rcases hab.2 with ⟨he, hn⟩ | ⟨he, hn⟩
  · exact (kappa_half hG (edge_kappa_ne_zero H hH ϕ hmu he)).resolve_right hn
  · exact ((kappa_half hG (edge_kappa_ne_zero H hH ϕ hmu he)).resolve_right hn).symm

lemma recorded_adj_lift (H : AbsForest n) (hH : H.IsValid)
    (ϕ : Fin H.k → Label n) {I : Db l G} (hI : H.IsDbOf l G ϕ I)
    {a c : ℕ} (hac : (recordedGraph l G I.2).Adj a c) :
    ∃ u v, (ϕ u).1 = a ∧ (ϕ v).1 = c ∧ H.graph.Adj u v := by
  have one : ∀ a c, (∃ (b : PClass n l) (j j' : Fin (classSize l G b)),
      I.2 b j = some j' ∧ a = ((edgeIdx l G b).symm j).1.tail ∧
      c = ((edgeIdx l G b).symm j').1.head n) →
      ∃ u v, (ϕ u).1 = a ∧ (ϕ v).1 = c ∧ H.graph.Adj u v := by
    rintro a c ⟨b, j, j', hj, rfl, rfl⟩
    obtain ⟨p, hp, h⟩ := (hI.2 b j j').mp hj
    dsimp only at h
    rcases h with h | h
    · exact ⟨p.1, p.2, h.2.2.1, h.2.2.2, edge_adj H hH hp⟩
    · exact ⟨p.2, p.1, h.2.2.1, h.2.2.2, (edge_adj H hH hp).symm⟩
  rcases hac.2 with h | h
  · exact one _ _ h
  · obtain ⟨u, v, hu, hv, huv⟩ := one _ _ h
    exact ⟨v, u, hv, hu, huv.symm⟩

lemma recorded_reachable_lift_from (H : AbsForest n) (hH : H.IsValid)
    (ϕ : Fin H.k → Label n) (hinj : Function.Injective ϕ)
    {I : Db l G} (hI : H.IsDbOf l G ϕ I) {a c : ℕ}
    (hac : (recordedGraph l G I.2).Reachable a c)
    (u : Fin H.k) (hu : (ϕ u).1 = a) :
    ∃ v, (ϕ v).1 = c ∧ H.graph.Reachable u v := by
  obtain ⟨w⟩ := hac
  induction w generalizing u with
  | nil => exact ⟨u, hu, .refl _⟩
  | cons hab w ih =>
    obtain ⟨x, y, hx, hy, hxy⟩ := recorded_adj_lift H hH ϕ hI hab
    have hux : u = x := hinj (Fin.ext (hu.trans hx.symm))
    obtain ⟨v, hv, hyv⟩ := ih y hy
    subst x
    exact ⟨v, hv, hxy.reachable.trans hyv⟩

lemma recorded_reachable_lift (H : AbsForest n) (hH : H.IsValid)
    (ϕ : Fin H.k → Label n) (hinj : Function.Injective ϕ)
    {I : Db l G} (hI : H.IsDbOf l G ϕ I) {a c : ℕ} (hne : a ≠ c)
    (hac : (recordedGraph l G I.2).Reachable a c) :
    ∃ u v, (ϕ u).1 = a ∧ (ϕ v).1 = c ∧ H.graph.Reachable u v := by
  obtain ⟨w⟩ := hac
  cases w with
  | nil => exact False.elim (hne rfl)
  | cons hab w =>
    obtain ⟨u, y, hu, hy, huy⟩ := recorded_adj_lift H hH ϕ hI hab
    obtain ⟨v, hv, hyv⟩ := recorded_reachable_lift_from H hH ϕ hinj hI w.reachable y hy
    exact ⟨u, v, hu, hv, huy.reachable.trans hyv⟩

lemma good_database_not_crossing (hG : G.IsValid) (hl : 1 ≤ l) (hln : l < n)
    (D : Description n) (hD : D.IsValid) (ϕ : Fin D.H.k → Label n)
    (hg : D.IsGood l G (Vbd n l) ϕ) (I : Db l G) (hI : D.H.IsDbOf l G ϕ I) :
    ¬ HasCrossing l G I.2 := by
  classical
  rintro ⟨a, c, ha, hacol, hc, hccol, hr⟩
  have hne : a ≠ c := by intro h; subst c; omega
  obtain ⟨u, v, hu, hv, huv⟩ := recorded_reachable_lift D.H hD.1 ϕ hg.2.2.2 hI hne hr
  obtain ⟨s, hs, _⟩ := hD.2 u
  have hsu := hs.2.symm
  have hsv := hsu.trans huv
  have hub : (ϕ u).1 ∈ Vbd n l := by
    exact Finset.mem_filter.mpr ⟨by simpa only [hu] using Finset.mem_range.mpr ha,
      Or.inl (by simpa only [hu] using hacol)⟩
  have hvb : (ϕ v).1 ∈ Vbd n l := by
    exact Finset.mem_filter.mpr ⟨by simpa only [hv] using Finset.mem_range.mpr hc,
      Or.inr (Or.inr (Or.inr (by simpa only [hv] using hccol)))⟩
  have hut : u ∈ D.H.Ctree ϕ s := by
    by_contra h
    exact hg.2.2.1 s hs.1 u hsu h hub
  have hvt : v ∈ D.H.Ctree ϕ s := by
    by_contra h
    exact hg.2.2.1 s hs.1 v hsv h hvb
  have htree : (D.H.treeGraph ϕ).Reachable u v :=
    (Finset.mem_filter.mp hut).2.symm.trans (Finset.mem_filter.mp hvt).2
  have hhalf := tree_reachable_half hG D.H hD.1 ϕ (ne_of_gt hg.1) htree
  rw [hu, hv, hacol, hccol] at hhalf
  omega

end WeldedPath.Supplement.CrossingExclusion

end

-- Solutions.WeldedPathConnectedReference
section

namespace WeldedPath.Supplement.ConnectedReference

open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}

lemma reachable_of_connected (H : AbsForest n) (s : Fin H.k)
    (hs : ∀ u, H.graph.Reachable s u) (u v : Fin H.k) : H.graph.Reachable u v :=
  (hs u).symm.trans (hs v)

lemma comp_eq_univ (H : AbsForest n) (s : Fin H.k)
    (hs : ∀ u, H.graph.Reachable s u) (u : Fin H.k) : H.comp u = Finset.univ := by
  classical
  ext v
  simp only [AbsForest.comp, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
  exact reachable_of_connected H s hs u v

lemma muComp_eq (H : AbsForest n) (s : Fin H.k)
    (hs : ∀ u, H.graph.Reachable s u) (u v : Fin H.k) (ϕ : Fin H.k → Label n) :
    H.muComp l G u ϕ = H.muComp l G v ϕ := by
  classical
  by_cases hk : H.k = 1
  · have huv : u = v := by
      apply Fin.ext
      have hu := u.isLt
      have hv := v.isLt
      omega
    rw [huv]
  · simp only [AbsForest.muComp, comp_eq_univ H s hs, Finset.card_univ,
      Fintype.card_fin, if_neg hk]

open Classical in
lemma comp_roots_eq_singleton (H : AbsForest n) (s : Fin H.k)
    (hs : ∀ u, H.graph.Reachable s u) (r : Fin H.k) (hr : H.IsCompRoot r) :
    (Finset.univ.filter fun u => H.IsCompRoot u) = {r} := by
  classical
  ext u
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro hu
    exact le_antisymm (hu r (reachable_of_connected H s hs u r))
      (hr u (reachable_of_connected H s hs r u))
  · intro h
    simpa only [h] using hr

lemma muRef_eq_muComp (H : AbsForest n) (s : Fin H.k)
    (hs : ∀ u, H.graph.Reachable s u) (ϕ : Fin H.k → Label n) :
    H.muRef l G ϕ = H.muComp l G s ϕ := by
  classical
  obtain ⟨r, hr, _⟩ := CrossingExclusion.comp_root_exists H s
  unfold AbsForest.muRef
  rw [comp_roots_eq_singleton H s hs r hr, Finset.prod_singleton]
  exact muComp_eq H s hs r s ϕ

lemma muComp_ne_zero_of_muRef_ne_zero (H : AbsForest n) (s : Fin H.k)
    (hs : ∀ u, H.graph.Reachable s u) (ϕ : Fin H.k → Label n)
    (hϕ : H.muRef l G ϕ ≠ 0) : H.muComp l G s ϕ ≠ 0 := by
  rwa [muRef_eq_muComp H s hs] at hϕ

lemma muComp_pos_of_muRef_pos (H : AbsForest n) (s : Fin H.k)
    (hs : ∀ u, H.graph.Reachable s u) (ϕ : Fin H.k → Label n)
    (hϕ : 0 < H.muRef l G ϕ) : 0 < H.muComp l G s ϕ := by
  rwa [muRef_eq_muComp H s hs] at hϕ

end WeldedPath.Supplement.ConnectedReference

end

-- Solutions.WeldedPathComponentTransport
section

namespace WeldedPath.Supplement.ComponentForest

open Classical ComponentRestriction ForestFactorization FiniteWeightedForest
open scoped BigOperators

variable {n : ℕ}

noncomputable def rootIndex (H : AbsForest n) (s : Fin H.k) :
    Fin (H.comp s).card := (vertexEquiv H s).symm ⟨s, root_mem_comp H s⟩

@[simp] lemma vertexMap_rootIndex (H : AbsForest n) (s : Fin H.k) :
    vertexMap H s (rootIndex H s) = s := by
  simp only [vertexMap, rootIndex, OrderIso.apply_symm_apply]

noncomputable def restrict (H : AbsForest n) (s : Fin H.k) (φ : Fin H.k → Label n) :
    Fin (H.comp s).card → Label n := fun i => φ (vertexMap H s i)

noncomputable def extend (H : AbsForest n) (s : Fin H.k)
    (ψ : Fin (H.comp s).card → Label n) : Fin H.k → Label n :=
  extendComponent H s (fun u => ψ ((vertexEquiv H s).symm u))

@[simp] lemma extend_vertexMap (H : AbsForest n) (s : Fin H.k)
    (ψ : Fin (H.comp s).card → Label n) (i : Fin (H.comp s).card) :
    extend H s ψ (vertexMap H s i) = ψ i := by
  simp only [extend, vertexMap, extendComponent_on, OrderIso.symm_apply_apply]

@[simp] lemma restrict_extend (H : AbsForest n) (s : Fin H.k)
    (ψ : Fin (H.comp s).card → Label n) : restrict H s (extend H s ψ) = ψ := by
  funext i
  exact extend_vertexMap H s ψ i

lemma extend_off (H : AbsForest n) (s : Fin H.k)
    (ψ : Fin (H.comp s).card → Label n) (u : Fin H.k) (hu : u ∉ H.comp s) :
    extend H s ψ u = 0 := by simp only [extend, extendComponent, dif_neg hu]

lemma extend_restrict (H : AbsForest n) (s : Fin H.k)
    (φ : Fin H.k → Label n) (hφ : ∀ u, u ∉ H.comp s → φ u = 0) :
    extend H s (restrict H s φ) = φ := by
  funext u
  by_cases hu : u ∈ H.comp s
  · simp only [extend, extendComponent, dif_pos hu, restrict, vertexMap,
      OrderIso.apply_symm_apply]
  · exact (extend_off H s _ u hu).trans (hφ u hu).symm

lemma comp_eq_univ (H : AbsForest n) (s : Fin H.k) (i : Fin (H.comp s).card) :
    (componentForest H s).comp i = Finset.univ := by
  apply Finset.eq_univ_iff_forall.mpr
  intro j
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, component_connected H s i j⟩

lemma component_card (H : AbsForest n) (s : Fin H.k) (i : Fin (H.comp s).card) :
    ((componentForest H s).comp i).card = (H.comp s).card := by
  rw [comp_eq_univ, Finset.card_univ, Fintype.card_fin]

lemma edgeMap_mem (H : AbsForest n) (s : Fin H.k)
    (e : Fin (H.comp s).card × Fin (H.comp s).card)
    (he : e ∈ (componentForest H s).E) : edgeMap H s e ∈ componentEdges H s :=
  Finset.mem_filter.mpr ⟨(mem_edges H s e).mp he, vertexMap_mem H s e.1⟩

lemma edgeMap_surj (H : AbsForest n) (hH : H.IsValid) (s : Fin H.k)
    (e : Fin H.k × Fin H.k) (he : e ∈ componentEdges H s) :
    ∃ f ∈ (componentForest H s).E, edgeMap H s f = e := by
  have hh := edge_endpoints_in_comp H hH s e he
  let f := ((vertexEquiv H s).symm ⟨e.1, hh.1⟩,
    (vertexEquiv H s).symm ⟨e.2, hh.2⟩)
  have hf : edgeMap H s f = e := by
    simp only [edgeMap, vertexMap, f, OrderIso.apply_symm_apply]
  exact ⟨f, (mem_edges H s f).mpr (hf.symm ▸ (Finset.mem_filter.mp he).1), hf⟩

lemma edgeWeight_restrict (l : ℕ) (G : WeldedInstance n) (H : AbsForest n)
    (hH : H.IsValid) (s : Fin H.k) (φ : Fin H.k → Label n) :
    edgeWeight (componentForest H s).E (componentKernel l G (componentForest H s))
        (restrict H s φ) =
      edgeWeight (componentEdges H s) (componentKernel l G H) φ := by
  apply Finset.prod_bij (fun e _ => edgeMap H s e)
  · exact edgeMap_mem H s
  · intro e _ f _ hef
    exact edgeMap_injective H s hef
  · intro e he
    obtain ⟨f, hf, hfe⟩ := edgeMap_surj H hH s e he
    exact ⟨f, hf, hfe⟩
  · intro e _
    rfl

lemma tree_adj_iff (H : AbsForest n) (s : Fin H.k) (φ : Fin H.k → Label n)
    (i j : Fin (H.comp s).card) :
    ((componentForest H s).treeGraph (restrict H s φ)).Adj i j ↔
      (H.treeGraph φ).Adj (vertexMap H s i) (vertexMap H s j) := by
  constructor
  · rintro ⟨hne, ⟨he, hw⟩ | ⟨he, hw⟩⟩
    · exact ⟨fun h => hne (vertexMap_injective H s h),
        Or.inl ⟨(mem_edges H s _).mp he, hw⟩⟩
    · exact ⟨fun h => hne (vertexMap_injective H s h),
        Or.inr ⟨(mem_edges H s _).mp he, hw⟩⟩
  · rintro ⟨hne, ⟨he, hw⟩ | ⟨he, hw⟩⟩
    · exact ⟨fun h => hne (congrArg (vertexMap H s) h),
        Or.inl ⟨(mem_edges H s _).mpr he, hw⟩⟩
    · exact ⟨fun h => hne (congrArg (vertexMap H s) h),
        Or.inr ⟨(mem_edges H s _).mpr he, hw⟩⟩

noncomputable def treeEmbedding (H : AbsForest n) (s : Fin H.k)
    (φ : Fin H.k → Label n) :
    (componentForest H s).treeGraph (restrict H s φ) ↪g H.treeGraph φ where
  toFun := vertexMap H s
  inj' := vertexMap_injective H s
  map_rel_iff' := (tree_adj_iff H s φ _ _).symm

noncomputable def treeIsoInduce (H : AbsForest n) (s : Fin H.k)
    (φ : Fin H.k → Label n) :
    (componentForest H s).treeGraph (restrict H s φ) ≃g
      (H.treeGraph φ).induce (↑(H.comp s) : Set (Fin H.k)) where
  __ := (vertexEquiv H s).toEquiv
  map_rel_iff' := (tree_adj_iff H s φ _ _).symm

lemma tree_reachable_iff (H : AbsForest n) (s : Fin H.k) (φ : Fin H.k → Label n)
    (i j : Fin (H.comp s).card) :
    ((componentForest H s).treeGraph (restrict H s φ)).Reachable i j ↔
      (H.treeGraph φ).Reachable (vertexMap H s i) (vertexMap H s j) := by
  constructor
  · exact fun h => h.map (treeEmbedding H s φ).toHom
  · rintro ⟨p⟩
    have hi := (Finset.mem_filter.mp (vertexMap_mem H s i)).2
    have hp : ∀ x ∈ p.support, x ∈ H.comp s := by
      intro x hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        hi.trans ((p.takeUntil x hx).reachable.mono (ForestOrder.treeGraph_le H φ))⟩
    have hm := (p.induce (↑(H.comp s) : Set (Fin H.k)) hp).reachable.map
      (treeIsoInduce H s φ).symm.toHom
    change ((componentForest H s).treeGraph (restrict H s φ)).Reachable
      ((vertexEquiv H s).symm (vertexEquiv H s i))
      ((vertexEquiv H s).symm (vertexEquiv H s j)) at hm
    simpa only [OrderIso.symm_apply_apply] using hm

lemma mem_ctree_iff (H : AbsForest n) (s : Fin H.k) (φ : Fin H.k → Label n)
    (i j : Fin (H.comp s).card) :
    j ∈ (componentForest H s).Ctree (restrict H s φ) i ↔
      vertexMap H s j ∈ H.Ctree φ (vertexMap H s i) := by
  simp only [AbsForest.Ctree, Finset.mem_filter, Finset.mem_univ, true_and]
  exact tree_reachable_iff H s φ i j

lemma mem_sfix_iff (H : AbsForest n) (hH : H.IsValid) (s : Fin H.k)
    (φ : Fin H.k → Label n) (i j : Fin (H.comp s).card) :
    j ∈ (componentForest H s).Sfix (restrict H s φ) i ↔
      vertexMap H s j ∈ H.Sfix φ (vertexMap H s i) := by
  simp only [AbsForest.Sfix, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (h | ⟨e, he, hw, hd⟩)
    · exact Or.inl ((mem_ctree_iff H s φ i j).mp h)
    · refine Or.inr ⟨edgeMap H s e, he, hw, ?_⟩
      rcases hd with ⟨hc, hj⟩ | ⟨hc, hj⟩
      · exact Or.inl ⟨(mem_ctree_iff H s φ i e.1).mp hc, congrArg (vertexMap H s) hj⟩
      · exact Or.inr ⟨(mem_ctree_iff H s φ i e.2).mp hc, congrArg (vertexMap H s) hj⟩
  · rintro (h | ⟨e, he, hw, hd⟩)
    · exact Or.inl ((mem_ctree_iff H s φ i j).mpr h)
    · have hecomp : e ∈ componentEdges H s := by
        apply Finset.mem_filter.mpr
        refine ⟨he, ?_⟩
        have hi := (Finset.mem_filter.mp (vertexMap_mem H s i)).2
        rcases hd with ⟨hc, _⟩ | ⟨hc, _⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            hi.trans ((Finset.mem_filter.mp hc).2.mono (ForestOrder.treeGraph_le H φ))⟩
        · have hc' := (Finset.mem_filter.mp hc).2.mono (ForestOrder.treeGraph_le H φ)
          have hadj : H.graph.Adj e.1 e.2 := ⟨ne_of_lt (hH.1 e he), Or.inl he⟩
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi.trans (hc'.trans hadj.symm.reachable)⟩
      obtain ⟨f, hf, hfe⟩ := edgeMap_surj H hH s e hecomp
      subst e
      refine Or.inr ⟨f, (mem_edges H s f).mp hf, hw, ?_⟩
      rcases hd with ⟨hc, hj⟩ | ⟨hc, hj⟩
      · exact Or.inl ⟨(mem_ctree_iff H s φ i f.1).mpr hc, vertexMap_injective H s hj⟩
      · exact Or.inr ⟨(mem_ctree_iff H s φ i f.2).mpr hc, vertexMap_injective H s hj⟩

theorem wfix_fiber_iff (H : AbsForest n) (hH : H.IsValid) (s : Fin H.k)
    (φ ψ : Fin H.k → Label n) (i : Fin (H.comp s).card) :
    (componentForest H s).Wfix (restrict H s φ) i =
        (componentForest H s).Wfix (restrict H s ψ) i ↔
      H.Wfix φ (vertexMap H s i) = H.Wfix ψ (vertexMap H s i) := by
  rw [FixedData.wfix_eq_iff_agree_sfix _ (component_valid H hH s),
    FixedData.wfix_eq_iff_agree_sfix H hH]
  constructor
  · intro h u hu
    have hucomp : u ∈ H.comp s := by
      have hi := (Finset.mem_filter.mp (vertexMap_mem H s i)).2
      have hr := ForestOrder.sfix_subset_comp H hH ψ (vertexMap H s i) hu
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi.trans (Finset.mem_filter.mp hr).2⟩
    let j := (vertexEquiv H s).symm ⟨u, hucomp⟩
    have hj : vertexMap H s j = u := by simp only [vertexMap, j, OrderIso.apply_symm_apply]
    have hh := h j ((mem_sfix_iff H hH s ψ i j).mpr (hj.symm ▸ hu))
    change φ (vertexMap H s j) = ψ (vertexMap H s j) at hh
    simpa only [hj] using hh
  · intro h j hj
    exact h _ ((mem_sfix_iff H hH s ψ i j).mp hj)

end WeldedPath.Supplement.ComponentForest

end

-- Solutions.WeldedPathComponentMeasure
section

namespace WeldedPath.Supplement.ComponentForest

open Classical ComponentRestriction ForestFactorization FiniteWeightedForest
open scoped BigOperators

variable {n : ℕ}

lemma componentEdges_eq (H : AbsForest n) (s : Fin H.k) (i : Fin (H.comp s).card) :
    componentEdges (componentForest H s) i = (componentForest H s).E := by
  simp only [componentEdges, comp_eq_univ, Finset.mem_univ, Finset.filter_true]

lemma forall_restrict_iff (H : AbsForest n) (s : Fin H.k) (φ : Fin H.k → Label n)
    (P : Label n → Prop) : (∀ i, P (restrict H s φ i)) ↔ ∀ u ∈ H.comp s, P (φ u) := by
  constructor
  · intro h u hu
    have hi := h ((vertexEquiv H s).symm ⟨u, hu⟩)
    simpa only [restrict, vertexMap, OrderIso.apply_symm_apply] using hi
  · intro h i
    exact h _ (vertexMap_mem H s i)

lemma forall_extend_iff (H : AbsForest n) (s : Fin H.k)
    (ψ : Fin (H.comp s).card → Label n) (P : Label n → Prop) :
    (∀ u ∈ H.comp s, P (extend H s ψ u)) ↔ ∀ i, P (ψ i) := by
  rw [← forall_restrict_iff, restrict_extend]

theorem supported_weight_sum (l : ℕ) (G : WeldedInstance n) (H : AbsForest n)
    (hH : H.IsValid) (s : Fin H.k) (V : Finset ℕ) :
    (∑ ψ ∈ Finset.univ.filter (fun ψ : Fin (H.comp s).card → Label n =>
      ∀ i, (ψ i).val ∈ V),
        edgeWeight (componentForest H s).E (componentKernel l G (componentForest H s)) ψ) =
      ∑ φ ∈ Finset.univ.filter (fun φ : Fin H.k → Label n =>
        (∀ u ∈ H.comp s, (φ u).val ∈ V) ∧ (∀ u, u ∉ H.comp s → φ u = 0)),
          edgeWeight (componentEdges H s) (componentKernel l G H) φ := by
  apply Finset.sum_bij (fun ψ _ => extend H s ψ)
  · intro ψ hψ
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (forall_extend_iff H s ψ (fun x : Label n => x.val ∈ V)).mpr
        (Finset.mem_filter.mp hψ).2, extend_off H s ψ⟩
  · intro ψ _ ψ' _ hh
    have h := congrArg (restrict H s) hh
    simpa only [restrict_extend] using h
  · intro φ hφ
    have hh := (Finset.mem_filter.mp hφ).2
    refine ⟨restrict H s φ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩,
      extend_restrict H s φ hh.2⟩
    exact (forall_restrict_iff H s φ (fun x : Label n => x.val ∈ V)).mpr hh.1
  · intro ψ _
    simpa only [restrict_extend] using edgeWeight_restrict l G H hH s (extend H s ψ)

theorem componentScale_eq (l : ℕ) (G : WeldedInstance n) (H : AbsForest n)
    (hH : H.IsValid) (s : Fin H.k) (i : Fin (H.comp s).card) :
    componentScale l G (componentForest H s) i = componentScale l G H s := by
  unfold componentScale
  simp only [comp_eq_univ, componentEdges_eq, Finset.mem_univ, forall_const,
    not_true_eq_false, false_implies, implies_true, and_true]
  rw [supported_weight_sum l G H hH s]

lemma componentCondition_restrict (l : ℕ) (H : AbsForest n)
    (s : Fin H.k) (φ : Fin H.k → Label n) :
    componentCondition l (componentForest H s) (rootIndex H s) (restrict H s φ) ↔
      componentCondition l H s φ := by
  unfold componentCondition
  rw [component_card]
  split_ifs
  · simp only [restrict, vertexMap_rootIndex]
  · rw [comp_eq_univ]
    simpa only [Finset.mem_univ, forall_const] using
      forall_restrict_iff H s φ (fun x => x.val ∈ Vmid n l ∪ Vbd n l)

theorem muComp_restrict_eq (l : ℕ) (G : WeldedInstance n) (H : AbsForest n)
    (hH : H.IsValid) (s : Fin H.k) (φ : Fin H.k → Label n) :
    (componentForest H s).muComp l G (rootIndex H s) (restrict H s φ) =
      H.muComp l G s φ := by
  rw [muComp_eq_componentCondition l G _ (component_valid H hH s),
    muComp_eq_componentCondition l G H hH,
    component_card, componentScale_eq l G H hH s, componentEdges_eq,
    edgeWeight_restrict l G H hH s, propext (componentCondition_restrict l H s φ)]

/-- Restriction to the actual connected subforest preserves the canonical
reference measure exactly, including its normalizing constant. -/
theorem muRef_restrict_eq (l : ℕ) (G : WeldedInstance n) (H : AbsForest n)
    (hH : H.IsValid) (s : Fin H.k) (φ : Fin H.k → Label n) :
    (componentForest H s).muRef l G (restrict H s φ) = H.muComp l G s φ := by
  rw [ConnectedReference.muRef_eq_muComp _ (rootIndex H s)
    (component_connected H s (rootIndex H s))]
  exact muComp_restrict_eq l G H hH s φ

theorem muRef_extend_eq (l : ℕ) (G : WeldedInstance n) (H : AbsForest n)
    (hH : H.IsValid) (s : Fin H.k) (ψ : Fin (H.comp s).card → Label n) :
    (componentForest H s).muRef l G ψ = H.muComp l G s (extend H s ψ) := by
  simpa only [restrict_extend] using muRef_restrict_eq l G H hH s (extend H s ψ)

theorem muRef_eq_product_restrictions (l : ℕ) (G : WeldedInstance n) (H : AbsForest n)
    (hH : H.IsValid) (φ : Fin H.k → Label n) :
    H.muRef l G φ = ∏ s ∈ Finset.univ.filter H.IsCompRoot,
      (componentForest H s).muRef l G (restrict H s φ) := by
  apply Finset.prod_congr rfl
  intro s _
  exact (muRef_restrict_eq l G H hH s φ).symm

end WeldedPath.Supplement.ComponentForest

end

-- Solutions.WeldedPathComponentCoordinates
section

namespace WeldedPath.Supplement.ComponentForest

open Classical ForestFactorization
open scoped BigOperators

variable {n : ℕ}

abbrev Roots (H : AbsForest n) := {s : Fin H.k // H.IsCompRoot s}

lemma vertexSigma_bijective (H : AbsForest n) :
    Function.Bijective (fun p : (Σ s : Roots H, Fin (H.comp s.val).card) =>
      vertexMap H p.1.val p.2) := by
  constructor
  · rintro ⟨a, i⟩ ⟨b, j⟩ hij
    change vertexMap H a.val i = vertexMap H b.val j at hij
    have hi := (Finset.mem_filter.mp (vertexMap_mem H a.val i)).2
    have hj := (Finset.mem_filter.mp (vertexMap_mem H b.val j)).2
    have hj' : H.graph.Reachable b.val (vertexMap H a.val i) := hij.symm ▸ hj
    have hab : a = b := Subtype.ext (le_antisymm (a.property _ (hi.trans hj'.symm))
      (b.property _ (hj'.trans hi.symm)))
    cases hab
    exact congrArg (Sigma.mk a) (vertexMap_injective H a.val hij)
  · intro u
    let s : Roots H := ⟨compRoot H u, compRoot_isRoot H u⟩
    have hu : u ∈ H.comp s.val :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, compRoot_reachable H u⟩
    refine ⟨⟨s, (vertexEquiv H s.val).symm ⟨u, hu⟩⟩, ?_⟩
    simp only [vertexMap, OrderIso.apply_symm_apply]

noncomputable def vertexSigmaEquiv (H : AbsForest n) :
    (Σ s : Roots H, Fin (H.comp s.val).card) ≃ Fin H.k :=
  Equiv.ofBijective _ (vertexSigma_bijective H)

/-- The assignments of the whole forest are exactly the independent
assignments on its connected restrictions. -/
noncomputable def assignmentEquiv (H : AbsForest n) :
    (Fin H.k → Label n) ≃ ((s : Roots H) → Fin (H.comp s.val).card → Label n) :=
  (Equiv.arrowCongr (vertexSigmaEquiv H) (Equiv.refl (Label n))).symm.trans
    (Equiv.piCurry (fun (s : Roots H) (_ : Fin (H.comp s.val).card) => Label n))

@[simp] theorem assignmentEquiv_apply (H : AbsForest n) (φ : Fin H.k → Label n)
    (s : Roots H) (i : Fin (H.comp s.val).card) :
    assignmentEquiv H φ s i = restrict H s.val φ i := rfl

theorem sum_assignments (H : AbsForest n) (f : (Fin H.k → Label n) → ℝ) :
    (∑ φ, f φ) = ∑ ψ, f ((assignmentEquiv H).symm ψ) :=
  ((assignmentEquiv H).symm.sum_comp f).symm

@[simp] theorem restrict_assignmentEquiv_symm (H : AbsForest n)
    (ψ : (s : Roots H) → Fin (H.comp s.val).card → Label n) (s : Roots H) :
    restrict H s.val ((assignmentEquiv H).symm ψ) = ψ s := by
  funext i
  exact congrArg (fun z => z s i) ((assignmentEquiv H).apply_symm_apply ψ)

theorem sum_component_card (H : AbsForest n) :
    (∑ s : Roots H, (H.comp s.val).card) = H.k := by
  simpa only [Fintype.card_sigma, Fintype.card_fin] using
    Fintype.card_congr (vertexSigmaEquiv H)

theorem muRef_eq_product_coordinates (l : ℕ) (G : WeldedInstance n)
    (H : AbsForest n) (hH : H.IsValid) (φ : Fin H.k → Label n) :
    H.muRef l G φ = ∏ s : Roots H,
      (componentForest H s.val).muRef l G (assignmentEquiv H φ s) := by
  rw [muRef_eq_product_restrictions l G H hH φ]
  exact Finset.prod_subtype (Finset.univ.filter H.IsCompRoot)
    (fun s => by simp only [Finset.mem_filter, Finset.mem_univ, true_and])
    (fun s => (componentForest H s).muRef l G (restrict H s φ))

end WeldedPath.Supplement.ComponentForest

end

-- Solutions.WeldedPathFixedDataSeparator
section

namespace WeldedPath.Supplement.FixedDataSeparator

open Classical FiniteWeightedForest

variable {n : ℕ} (H : AbsForest n) (φ : Fin H.k → Label n)
  (e : Fin H.k × Fin H.k) (P : Fin H.k → Prop)

/-- Once a cut edge is a weld, the tree component cannot cross that cut. -/
theorem ctree_on_side
    (hcut : ∀ p ∈ H.E, p ≠ e → (P p.1 ↔ P p.2)) (hw : H.IsWeldUnder φ e)
    (v : Fin H.k) (hv : P v) : ∀ u ∈ H.Ctree φ v, P u := by
  intro u hu
  have hr : (H.treeGraph φ).Reachable v u := (Finset.mem_filter.mp hu).2
  apply FixedData.reachable_closed P _ hr hv
  intro x y hx hxy
  rcases hxy with ⟨hne, ⟨hp, hnw⟩ | ⟨hp, hnw⟩⟩
  · have hpe : (x, y) ≠ e := by
      intro he
      apply hnw
      simpa only [he] using hw
    exact (hcut (x, y) hp hpe).mp hx
  · have hpe : (y, x) ≠ e := by
      intro he
      apply hnw
      simpa only [he] using hw
    exact (hcut (y, x) hp hpe).mpr hx

/-- Fixed data on one side can include the opposite endpoint of the bridge,
but cannot include any other vertex across the bridge. -/
theorem sfix_on_side_or_endpoints
    (hcut : ∀ p ∈ H.E, p ≠ e → (P p.1 ↔ P p.2)) (hw : H.IsWeldUnder φ e)
    (v : Fin H.k) (hv : P v) :
    ∀ u ∈ H.Sfix φ v, P u ∨ u = e.1 ∨ u = e.2 := by
  intro u hu
  rcases Finset.mem_union.mp hu with hu | hu
  · exact Or.inl (ctree_on_side H φ e P hcut hw v hv u hu)
  · obtain ⟨p, hp, _, ht⟩ := (Finset.mem_filter.mp hu).2
    by_cases hpe : p = e
    · subst p
      rcases ht with ht | ht
      · exact Or.inr (Or.inr ht.2.symm)
      · exact Or.inr (Or.inl ht.2.symm)
    · apply Or.inl
      rcases ht with ⟨ht, rfl⟩ | ⟨ht, rfl⟩
      · exact (hcut p hp hpe).mp (ctree_on_side H φ e P hcut hw v hv p.1 ht)
      · exact (hcut p hp hpe).mpr (ctree_on_side H φ e P hcut hw v hv p.2 ht)

/-- The exact measurability statement used for centered branch coefficients:
on the weld event, Wfix is determined by one side and the two endpoint labels. -/
theorem wfix_depends_on_side (hH : H.IsValid)
    (hcut : ∀ p ∈ H.E, p ≠ e → (P p.1 ↔ P p.2)) (hw : H.IsWeldUnder φ e)
    (v : Fin H.k) (hv : P v) (ψ : Fin H.k → Label n)
    (hagree : ∀ u, P u ∨ u = e.1 ∨ u = e.2 → φ u = ψ u) :
    H.Wfix φ v = H.Wfix ψ v := by
  symm
  apply FixedData.wfix_eq_of_agree_sfix H hH ψ φ v
  intro u hu
  exact (hagree u (sfix_on_side_or_endpoints H φ e P hcut hw v hv u hu)).symm

/-- The preceding measurability theorem on the actual component obtained by
erasing a stored forest edge. -/
theorem wfix_depends_on_deleted_component (hH : H.IsValid)
    (hw : H.IsWeldUnder φ e) (v : Fin H.k)
    (hv : (edgeGraph (H.E.erase e)).Reachable e.1 v)
    (ψ : Fin H.k → Label n)
    (hagree : ∀ u, (edgeGraph (H.E.erase e)).Reachable e.1 u ∨ u = e.1 ∨ u = e.2 →
      φ u = ψ u) : H.Wfix φ v = H.Wfix ψ v := by
  apply wfix_depends_on_side H φ e _ hH _ hw v hv ψ hagree
  intro p hp hpe
  exact forest_cut_closed H.E e hH.1 p (Finset.mem_erase.mpr ⟨hpe, hp⟩)

end WeldedPath.Supplement.FixedDataSeparator

end

-- Solutions.WeldedPathBoundaryCoefficients
section

namespace WeldedPath.Supplement.BoundaryCoefficients

open scoped BigOperators

variable {n : ℕ} (H : AbsForest n) (φ : Fin H.k → Label n)

theorem ctree_mem_symm (a u : Fin H.k) :
    a ∈ H.Ctree φ u ↔ u ∈ H.Ctree φ a := by
  classical
  simp only [AbsForest.Ctree, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨SimpleGraph.Reachable.symm, SimpleGraph.Reachable.symm⟩

theorem ctree_eq_of_mem (a u : Fin H.k) (ha : a ∈ H.Ctree φ u) :
    H.Ctree φ u = H.Ctree φ a := by
  classical
  have hr : (H.treeGraph φ).Reachable u a := (Finset.mem_filter.mp ha).2
  ext v
  simp only [AbsForest.Ctree, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun hv => hr.symm.trans hv, fun hv => hr.trans hv⟩

theorem wfix_eq_of_mem (a u : Fin H.k) (ha : a ∈ H.Ctree φ u) :
    H.Wfix φ u = H.Wfix φ a := by
  have hC := ctree_eq_of_mem H φ a u ha
  have hS : H.Sfix φ u = H.Sfix φ a := by
    classical
    simp only [AbsForest.Sfix, hC]
  simp only [AbsForest.Wfix, hC, hS]

/-- If a coefficient is allowed only when a fixed nonempty set lies in the
selected tree component, the apparent choice of selected root disappears:
the entire sum is a single function of the data at any vertex of that set. -/
theorem boundary_coefficient_sum (F : Finset (Fin H.k)) (a : Fin H.k) (ha : a ∈ F)
    (h : Fin H.k →
      (Finset (Fin H.k) × Finset (Fin H.k × ℕ) × Finset (Fin H.k × ℕ)) → ℂ) :
    (∑ u, if F ⊆ H.Ctree φ u then h u (H.Wfix φ u) else 0) =
      if F ⊆ H.Ctree φ a then
        ∑ u ∈ H.Ctree φ a, h u (H.Wfix φ a) else 0 := by
  classical
  have he (u : Fin H.k) :
      (F ⊆ H.Ctree φ u) ↔ (F ⊆ H.Ctree φ a ∧ u ∈ H.Ctree φ a) := by
    constructor
    · intro hF
      have hua := hF ha
      exact ⟨by simpa only [ctree_eq_of_mem H φ a u hua] using hF,
        (ctree_mem_symm H φ a u).mp hua⟩
    · rintro ⟨hF, hu⟩
      simpa only [ctree_eq_of_mem H φ u a hu] using hF
  by_cases hF : F ⊆ H.Ctree φ a
  · rw [if_pos hF]
    calc
      _ = ∑ u, if u ∈ H.Ctree φ a then h u (H.Wfix φ a) else 0 := by
        apply Finset.sum_congr rfl
        intro u _
        by_cases hu : u ∈ H.Ctree φ a
        · have hua := (ctree_mem_symm H φ a u).mpr hu
          simp only [if_pos ((he u).mpr ⟨hF, hu⟩), if_pos hu,
            wfix_eq_of_mem H φ a u hua]
        · simp only [if_neg (fun hs => hu ((he u).mp hs).2), if_neg hu]
      _ = _ := by rw [← Finset.sum_filter]; simp
  · rw [if_neg hF]
    apply Finset.sum_eq_zero
    intro u _
    exact if_neg (fun hs => hF ((he u).mp hs).1)

end WeldedPath.Supplement.BoundaryCoefficients

end

-- Solutions.WeldedPathFixedDataFunctions
section

namespace WeldedPath.Supplement.FixedDataFunctions

open Classical

variable {n : ℕ}

abbrev Data (H : AbsForest n) :=
  Finset (Fin H.k) × Finset (Fin H.k × ℕ) × Finset (Fin H.k × ℕ)

/-- The fixed data at either endpoint records the labels of both endpoints
of every incident stored edge, whether that edge is a weld or a tree edge. -/
theorem endpoint_pair_factors_left (H : AbsForest n) (hH : H.IsValid)
    (e : Fin H.k × Fin H.k) (he : e ∈ H.E) :
    Function.FactorsThrough (fun φ : Fin H.k → Label n => (φ e.1, φ e.2))
      (fun φ => H.Wfix φ e.1) := by
  intro φ ψ hd
  have hr : e.1 ∈ H.Ctree ψ e.1 := by simp [AbsForest.Ctree]
  obtain ⟨h₁, h₂⟩ := FixedData.edge_endpoints_mem_sfix H hH ψ e.1 e he (Or.inl hr)
  have ha := (FixedData.wfix_eq_iff_agree_sfix H hH φ ψ e.1).mp hd
  exact Prod.ext (ha e.1 h₁) (ha e.2 h₂)

theorem endpoint_pair_factors_right (H : AbsForest n) (hH : H.IsValid)
    (e : Fin H.k × Fin H.k) (he : e ∈ H.E) :
    Function.FactorsThrough (fun φ : Fin H.k → Label n => (φ e.1, φ e.2))
      (fun φ => H.Wfix φ e.2) := by
  intro φ ψ hd
  have hr : e.2 ∈ H.Ctree ψ e.2 := by simp [AbsForest.Ctree]
  obtain ⟨h₁, h₂⟩ := FixedData.edge_endpoints_mem_sfix H hH ψ e.2 e he (Or.inr hr)
  have ha := (FixedData.wfix_eq_iff_agree_sfix H hH φ ψ e.2).mp hd
  exact Prod.ext (ha e.1 h₁) (ha e.2 h₂)

theorem endpoint_function_exists_left (H : AbsForest n) (hH : H.IsValid)
    (e : Fin H.k × Fin H.k) (he : e ∈ H.E) (f : Label n × Label n → ℂ) :
    ∃ g : Data H → ℂ, ∀ φ : Fin H.k → Label n, f (φ e.1, φ e.2) = g (H.Wfix φ e.1) := by
  obtain ⟨g, hg⟩ := (Function.factorsThrough_iff _).mp
    ((endpoint_pair_factors_left H hH e he).comp_left f)
  exact ⟨g, fun φ => congrFun hg φ⟩

theorem endpoint_function_exists_right (H : AbsForest n) (hH : H.IsValid)
    (e : Fin H.k × Fin H.k) (he : e ∈ H.E) (f : Label n × Label n → ℂ) :
    ∃ g : Data H → ℂ, ∀ φ : Fin H.k → Label n, f (φ e.1, φ e.2) = g (H.Wfix φ e.2) := by
  obtain ⟨g, hg⟩ := (Function.factorsThrough_iff _).mp
    ((endpoint_pair_factors_right H hH e he).comp_left f)
  exact ⟨g, fun φ => congrFun hg φ⟩

theorem wfix_eq_on_nonweld_edge (H : AbsForest n) (hH : H.IsValid)
    (e : Fin H.k × Fin H.k) (he : e ∈ H.E) (φ : Fin H.k → Label n)
    (hw : ¬H.IsWeldUnder φ e) : H.Wfix φ e.1 = H.Wfix φ e.2 := by
  have hr : (H.treeGraph φ).Reachable e.1 e.2 :=
    SimpleGraph.Adj.reachable ⟨ne_of_lt (hH.1 e he), Or.inl ⟨he, hw⟩⟩
  have hm : e.1 ∈ H.Ctree φ e.2 :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr.symm⟩
  exact (BoundaryCoefficients.wfix_eq_of_mem H φ e.1 e.2 hm).symm

/-- The nonweld part of a child-local coefficient already belongs to the
parent-local coefficient space. -/
theorem nonweld_transfer (H : AbsForest n) (hH : H.IsValid)
    (e : Fin H.k × Fin H.k) (he : e ∈ H.E) (h : Data H → ℂ) (φ : Fin H.k → Label n) :
    (if H.IsWeldUnder φ e then 0 else h (H.Wfix φ e.1)) =
      if H.IsWeldUnder φ e then 0 else h (H.Wfix φ e.2) := by
  by_cases hw : H.IsWeldUnder φ e
  · simp [hw]
  · simp [hw, wfix_eq_on_nonweld_edge H hH e he φ hw]

/-- On the weld event, a local coefficient sees only its side of the cut
and the opposite endpoint label. -/
theorem weld_coefficient_factors_left (H : AbsForest n) (hH : H.IsValid)
    (e : Fin H.k × Fin H.k) (P : Fin H.k → Prop)
    (hcut : ∀ p ∈ H.E, p ≠ e → (P p.1 ↔ P p.2)) (hleft : P e.1)
    (v : Fin H.k) (hv : P v) (h : Data H → ℂ) :
    Function.FactorsThrough
      (fun φ : Fin H.k → Label n => if H.IsWeldUnder φ e then h (H.Wfix φ v) else 0)
      (fun φ => (φ e.2, fun a : {a // P a} => φ a)) := by
  intro φ ψ hd
  dsimp only at hd ⊢
  have h₂ : φ e.2 = ψ e.2 := congrArg Prod.fst hd
  have hs : ∀ a, P a → φ a = ψ a := by
    intro a ha
    exact congrFun (congrArg Prod.snd hd) ⟨a, ha⟩
  have h₁ := hs e.1 hleft
  have hwiff : H.IsWeldUnder φ e ↔ H.IsWeldUnder ψ e := by
    simp only [AbsForest.IsWeldUnder, h₁, h₂]
  by_cases hw : H.IsWeldUnder φ e
  · rw [if_pos hw, if_pos (hwiff.mp hw)]
    apply congrArg h
    apply FixedDataSeparator.wfix_depends_on_side H φ e P hH hcut hw v hv ψ
    intro a ha
    rcases ha with ha | rfl | rfl
    · exact hs a ha
    · exact h₁
    · exact h₂
  · rw [if_neg hw, if_neg (mt hwiff.mpr hw)]

theorem weld_coefficient_exists_left (H : AbsForest n) (hH : H.IsValid)
    (e : Fin H.k × Fin H.k) (P : Fin H.k → Prop)
    (hcut : ∀ p ∈ H.E, p ≠ e → (P p.1 ↔ P p.2)) (hleft : P e.1)
    (v : Fin H.k) (hv : P v) (h : Data H → ℂ) :
    ∃ f : Label n → ({a // P a} → Label n) → ℂ,
      ∀ φ : Fin H.k → Label n,
        (if H.IsWeldUnder φ e then h (H.Wfix φ v) else 0) =
          f (φ e.2) (fun a => φ a) := by
  obtain ⟨f, hf⟩ := (Function.factorsThrough_iff _).mp
    (weld_coefficient_factors_left H hH e P hcut hleft v hv h)
  exact ⟨fun x a => f (x, a), fun φ => congrFun hf φ⟩

end WeldedPath.Supplement.FixedDataFunctions

end

-- Solutions.WeldedPathComponentData
section

namespace WeldedPath.Supplement.ComponentForest

open Classical ComponentRestriction FixedDataFunctions

variable {n : ℕ}

lemma ctree_subset_component (H : AbsForest n) (s : Fin H.k)
    (φ : Fin H.k → Label n) (i : Fin (H.comp s).card) :
    H.Ctree φ (vertexMap H s i) ⊆ H.comp s := by
  intro u hu
  have hi := (Finset.mem_filter.mp (vertexMap_mem H s i)).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    hi.trans ((Finset.mem_filter.mp hu).2.mono (ForestOrder.treeGraph_le H φ))⟩

lemma sfix_subset_component (H : AbsForest n) (hH : H.IsValid) (s : Fin H.k)
    (φ : Fin H.k → Label n) (i : Fin (H.comp s).card) :
    H.Sfix φ (vertexMap H s i) ⊆ H.comp s := by
  intro u hu
  have hi := (Finset.mem_filter.mp (vertexMap_mem H s i)).2
  have hu' := ForestOrder.sfix_subset_comp H hH φ (vertexMap H s i) hu
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi.trans (Finset.mem_filter.mp hu').2⟩

theorem ctree_image (H : AbsForest n) (s : Fin H.k) (φ : Fin H.k → Label n)
    (i : Fin (H.comp s).card) :
    ((componentForest H s).Ctree (restrict H s φ) i).image (vertexMap H s) =
      H.Ctree φ (vertexMap H s i) := by
  ext u
  constructor
  · intro hu
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hu
    exact (mem_ctree_iff H s φ i j).mp hj
  · intro hu
    let j := (vertexEquiv H s).symm ⟨u, ctree_subset_component H s φ i hu⟩
    have hj : vertexMap H s j = u := by
      simp only [vertexMap, j, OrderIso.apply_symm_apply]
    exact Finset.mem_image.mpr ⟨j, (mem_ctree_iff H s φ i j).mpr (hj.symm ▸ hu), hj⟩

theorem sfix_image (H : AbsForest n) (hH : H.IsValid) (s : Fin H.k)
    (φ : Fin H.k → Label n) (i : Fin (H.comp s).card) :
    ((componentForest H s).Sfix (restrict H s φ) i).image (vertexMap H s) =
      H.Sfix φ (vertexMap H s i) := by
  ext u
  constructor
  · intro hu
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hu
    exact (mem_sfix_iff H hH s φ i j).mp hj
  · intro hu
    let j := (vertexEquiv H s).symm ⟨u, sfix_subset_component H hH s φ i hu⟩
    have hj : vertexMap H s j = u := by
      simp only [vertexMap, j, OrderIso.apply_symm_apply]
    exact Finset.mem_image.mpr ⟨j, (mem_sfix_iff H hH s φ i j).mpr (hj.symm ▸ hu), hj⟩

noncomputable def dataLift (H : AbsForest n) (s : Fin H.k)
    (d : Data (componentForest H s)) : Data H :=
  (d.1.image (vertexMap H s),
    d.2.1.image (fun p => (vertexMap H s p.1, p.2)),
    d.2.2.image (fun p => (vertexMap H s p.1, p.2)))

theorem dataLift_injective (H : AbsForest n) (s : Fin H.k) :
    Function.Injective (dataLift H s) := by
  have hp : Function.Injective (fun p : Fin (H.comp s).card × ℕ =>
      (vertexMap H s p.1, p.2)) := by
    intro p q hpq
    have h₁ := congrArg (fun z : Fin H.k × ℕ => z.1) hpq
    have h₂ := congrArg (fun z : Fin H.k × ℕ => z.2) hpq
    exact Prod.ext (vertexMap_injective H s h₁) h₂
  intro d e hde
  exact Prod.ext (Finset.image_injective (vertexMap_injective H s) (congrArg Prod.fst hde))
    (Prod.ext (Finset.image_injective hp (congrArg (fun x => x.2.1) hde))
      (Finset.image_injective hp (congrArg (fun x => x.2.2) hde)))

/-- Fixed data on the connected restriction is the original fixed data with
its abstract vertex identifiers relabeled by the increasing component map. -/
theorem dataLift_wfix (H : AbsForest n) (hH : H.IsValid) (s : Fin H.k)
    (φ : Fin H.k → Label n) (i : Fin (H.comp s).card) :
    dataLift H s ((componentForest H s).Wfix (restrict H s φ) i) =
      H.Wfix φ (vertexMap H s i) := by
  apply Prod.ext
  · exact ctree_image H s φ i
  · apply Prod.ext
    · change (((componentForest H s).Ctree (restrict H s φ) i).image
        (fun j => (j, (restrict H s φ j).val))).image
          (fun p => (vertexMap H s p.1, p.2)) =
        (H.Ctree φ (vertexMap H s i)).image (fun u => (u, (φ u).val))
      rw [← ctree_image H s φ i]
      simp only [Finset.image_image]
      rfl
    · change ((((componentForest H s).Sfix (restrict H s φ) i) \
          ((componentForest H s).Ctree (restrict H s φ) i)).image
        (fun j => (j, (restrict H s φ j).val))).image
          (fun p => (vertexMap H s p.1, p.2)) =
        ((H.Sfix φ (vertexMap H s i)) \ (H.Ctree φ (vertexMap H s i))).image
          (fun u => (u, (φ u).val))
      rw [← sfix_image H hH s φ i, ← ctree_image H s φ i,
        ← Finset.image_sdiff _ _ (vertexMap_injective H s)]
      simp only [Finset.image_image]
      rfl

lemma component_k_le (H : AbsForest n) (s : Fin H.k) :
    (componentForest H s).k ≤ H.k := by
  simpa only [componentForest, Finset.card_univ, Fintype.card_fin] using
    Finset.card_le_univ (H.comp s)

theorem avoid_ctree_restrict_iff (H : AbsForest n) (s : Fin H.k)
    (φ : Fin H.k → Label n) (i : Fin (H.comp s).card) (B : Finset ℕ) :
    (∀ j, j ∉ (componentForest H s).Ctree (restrict H s φ) i →
      (restrict H s φ j).val ∉ B) ↔
    (∀ u ∈ H.comp s, u ∉ H.Ctree φ (vertexMap H s i) → (φ u).val ∉ B) := by
  constructor
  · intro h u hu htree
    let j := (vertexEquiv H s).symm ⟨u, hu⟩
    have hj : vertexMap H s j = u := by
      simp only [vertexMap, j, OrderIso.apply_symm_apply]
    have hjtree : j ∉ (componentForest H s).Ctree (restrict H s φ) i := by
      intro hc
      exact htree (hj ▸ (mem_ctree_iff H s φ i j).mp hc)
    simpa only [restrict, hj] using h j hjtree
  · intro h j hj
    exact h _ (vertexMap_mem H s j) (fun hc => hj ((mem_ctree_iff H s φ i j).mpr hc))

end WeldedPath.Supplement.ComponentForest

end

-- Solutions.WeldedPathHilbertSupport
section

namespace WeldedPath.HilbertSupport

open scoped BigOperators

variable {X Y A : Type*} [Fintype X] [Fintype Y] [Fintype A]

theorem ketBra_apply (u : Hil Y) (v ψ : Hil X) :
    ketBra u v ψ = inner ℂ v ψ • u := rfl

theorem inner_ket [DecidableEq X] (x : X) (ψ : Hil X) :
    inner ℂ (ket x) ψ = ψ x := by
  simp [ket, EuclideanSpace.inner_single_left]

theorem ket_apply [DecidableEq X] (x y : X) :
    ket x y = if y = x then 1 else 0 := by
  simp [ket, PiLp.single_apply]

theorem ketTensor_apply (u : Hil A) (v : Hil X) (a : A) (x : X) :
    ketTensor u v (a, x) = u a * v x := rfl

theorem sum_basis [DecidableEq X] (ψ : Hil X) :
    (∑ x, ψ x • ket x) = ψ := by
  ext y
  simp [ket_apply]

theorem diagProj_apply [DecidableEq X] (P : X → Prop) [DecidablePred P]
    (ψ : Hil X) (x : X) :
    diagProj P ψ x = if P x then ψ x else 0 := by
  simp [diagProj, ketBra_apply, inner_ket, ket_apply]

theorem diagProj_zero_iff [DecidableEq X] (P : X → Prop) [DecidablePred P]
    (ψ : Hil X) : diagProj P ψ = 0 ↔ ∀ x, P x → ψ x = 0 := by
  constructor
  · intro h x hx
    have he := congrArg (fun v : Hil X => v x) h
    simpa [diagProj_apply, hx] using he
  · intro h
    ext x
    by_cases hx : P x <;> simp [diagProj_apply, hx, h]

theorem diagProj_norm_le [DecidableEq X] (P : X → Prop) [DecidablePred P]
    (ψ : Hil X) : ‖diagProj P ψ‖ ≤ ‖ψ‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : P x
  · simp [diagProj_apply, hx]
  · simp [diagProj_apply, hx]

theorem diagProj_ket [DecidableEq X] (P : X → Prop) [DecidablePred P] (x : X) :
    diagProj P (ket x) = if P x then ket x else 0 := by
  ext y
  by_cases hx : P x <;> by_cases hy : y = x <;>
    simp_all [diagProj_apply, ket_apply]

theorem opTensor_ket [DecidableEq A] [DecidableEq X]
    {B : Type*} [Fintype B] (S : Hil A →L[ℂ] Hil B) (T : Hil X →L[ℂ] Hil Y)
    (a : A) (x : X) :
    opTensor S T (ket (a, x)) = ketTensor (S (ket a)) (T (ket x)) := by
  simp [opTensor, ketBra_apply, inner_ket, ket_apply]

theorem tensor_ket_eq [DecidableEq A] [DecidableEq X] (a : A) (x : X) :
    ketTensor (ket a) (ket x) = ket (a, x) := by
  ext p
  obtain ⟨b, y⟩ := p
  by_cases ha : b = a <;> by_cases hx : y = x <;>
    simp [ketTensor_apply, ket_apply, ha, hx, Prod.mk.injEq]

theorem diagProj_tensor_zero [DecidableEq A] [DecidableEq X]
    (P : X → Prop) [DecidablePred P] (u : Hil A) (v : Hil X)
    (hv : ∀ x, P x → v x = 0) :
    diagProj (fun p : A × X => P p.2) (ketTensor u v) = 0 := by
  apply (diagProj_zero_iff _ _).mpr
  rintro ⟨a, x⟩ hx
  simp [ketTensor_apply, hv x hx]

theorem tensor_projector_annihilates [DecidableEq A] [DecidableEq X]
    (P : X → Prop) [DecidablePred P] (K : Submodule ℂ (Hil X))
    (hK : ∀ v ∈ K, ∀ x, P x → v x = 0) :
    (diagProj (fun p : A × X => P p.2)).comp
      (opTensor (1 : Hil A →L[ℂ] Hil A) K.starProjection) = 0 := by
  apply ContinuousLinearMap.ext
  intro ψ
  rw [← sum_basis ψ]
  simp only [map_sum, map_smul, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.zero_apply, smul_zero, Finset.sum_const_zero]
  apply Finset.sum_eq_zero
  intro p _
  rw [opTensor_ket]
  have hz := diagProj_tensor_zero P (ket p.1) (K.starProjection (ket p.2))
    (hK _ (K.starProjection_apply_mem _) )
  simpa using congrArg (fun v => ψ p • v) hz

end WeldedPath.HilbertSupport

end

-- Solutions.WeldedPathComponentRegroup
section

namespace WeldedPath.Supplement.ComponentForest

open Classical QAlgorithms HilbertSupport
open scoped BigOperators

variable {n : ℕ}

section Generic

variable {I : Type*} [Fintype I] [DecidableEq I]

abbrev ExceptTwo (a b : I) := {i : I // i ≠ a ∧ i ≠ b}

noncomputable def twoPiEquiv (A : I → Type*) (a b : I) (hab : a ≠ b) :
    ((i : I) → A i) ≃ ((A a × A b) × ((i : ExceptTwo a b) → A i.val)) where
  toFun f := ((f a, f b), fun i => f i.val)
  invFun p i := if ha : i = a then ha.symm.rec p.1.1 else
    if hb : i = b then hb.symm.rec p.1.2 else p.2 ⟨i, ha, hb⟩
  left_inv f := by
    funext i
    dsimp only
    split_ifs with ha hb
    · subst i; rfl
    · subst i; rfl
    · rfl
  right_inv p := by
    apply Prod.ext
    · apply Prod.ext
      · simp
      · simp [hab.symm]
    · funext i
      simp only [dif_neg i.property.1, dif_neg i.property.2]

@[simp] theorem twoPiEquiv_apply (A : I → Type*) (a b : I) (hab : a ≠ b)
    (f : (i : I) → A i) :
    twoPiEquiv A a b hab f = ((f a, f b), fun i : ExceptTwo a b => f i.val) := rfl

@[simp] theorem twoPiEquiv_symm_first (A : I → Type*) (a b : I) (hab : a ≠ b)
    (p : (A a × A b) × ((i : ExceptTwo a b) → A i.val)) :
    (twoPiEquiv A a b hab).symm p a = p.1.1 :=
  congrArg (fun z => z.1.1) ((twoPiEquiv A a b hab).apply_symm_apply p)

@[simp] theorem twoPiEquiv_symm_second (A : I → Type*) (a b : I) (hab : a ≠ b)
    (p : (A a × A b) × ((i : ExceptTwo a b) → A i.val)) :
    (twoPiEquiv A a b hab).symm p b = p.1.2 :=
  congrArg (fun z => z.1.2) ((twoPiEquiv A a b hab).apply_symm_apply p)

@[simp] theorem twoPiEquiv_symm_rest (A : I → Type*) (a b : I) (hab : a ≠ b)
    (p : (A a × A b) × ((i : ExceptTwo a b) → A i.val)) (i : ExceptTwo a b) :
    (twoPiEquiv A a b hab).symm p i.val = p.2 i :=
  congrArg (fun z => z.2 i) ((twoPiEquiv A a b hab).apply_symm_apply p)

theorem prod_one {M : Type*} [CommMonoid M] (f : I → M) (a : I) :
    (∏ i, f i) = f a * ∏ i : {i : I // i ≠ a}, f i.val := by
  rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ a)]
  congr 1
  exact Finset.prod_subtype _ (fun i => by simp only [Finset.mem_erase,
    Finset.mem_univ, and_true]) f

theorem prod_two {M : Type*} [CommMonoid M] (f : I → M) (a b : I) (hab : a ≠ b) :
    (∏ i, f i) = (f a * f b) * ∏ i : ExceptTwo a b, f i.val := by
  have hb : b ∈ Finset.univ.erase a := by
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    exact hab.symm
  calc
    _ = f a * ∏ i ∈ Finset.univ.erase a, f i :=
      (Finset.mul_prod_erase _ f (Finset.mem_univ a)).symm
    _ = f a * (f b * ∏ i ∈ (Finset.univ.erase a).erase b, f i) := by
      rw [Finset.mul_prod_erase _ f hb]
    _ = (f a * f b) * ∏ i : ExceptTwo a b, f i.val := by
      rw [← mul_assoc]
      congr 1
      exact Finset.prod_subtype _ (fun i => by
        simp only [Finset.mem_erase, Finset.mem_univ, and_true, true_and, and_comm]) f

theorem twoPiEquiv_prod {M : Type*} [CommMonoid M] (A : I → Type*)
    (w : (i : I) → A i → M) (a b : I) (hab : a ≠ b)
    (p : (A a × A b) × ((i : ExceptTwo a b) → A i.val)) :
    (∏ i, w i ((twoPiEquiv A a b hab).symm p i)) =
      (w a p.1.1 * w b p.1.2) * ∏ i : ExceptTwo a b, w i.val (p.2 i) := by
  rw [prod_two _ a b hab]
  simp only [twoPiEquiv_symm_first, twoPiEquiv_symm_second, twoPiEquiv_symm_rest]

end Generic

abbrev LocalAssignment (H : AbsForest n) (s : Roots H) :=
  Fin (H.comp s.val).card → Label n

@[simp] theorem assignmentEquiv_restrict (H : AbsForest n) (φ : Fin H.k → Label n)
    (s : Roots H) : assignmentEquiv H φ s = restrict H s.val φ := rfl

abbrev OneSpectator (H : AbsForest n) (a : Roots H) :=
  (s : {s : Roots H // s ≠ a}) → LocalAssignment H s.val

abbrev TwoSpectator (H : AbsForest n) (a b : Roots H) :=
  (s : ExceptTwo a b) → LocalAssignment H s.val

noncomputable def regroupOne (H : AbsForest n) (a : Roots H) :
    (Fin H.k → Label n) ≃ LocalAssignment H a × OneSpectator H a :=
  (assignmentEquiv H).trans (Equiv.piSplitAt a (LocalAssignment H))

noncomputable def regroupTwo (H : AbsForest n) (a b : Roots H) (hab : a ≠ b) :
    (Fin H.k → Label n) ≃ (LocalAssignment H a × LocalAssignment H b) × TwoSpectator H a b :=
  (assignmentEquiv H).trans (twoPiEquiv (LocalAssignment H) a b hab)

@[simp] theorem regroupOne_apply (H : AbsForest n) (a : Roots H) (φ : Fin H.k → Label n) :
    regroupOne H a φ = (restrict H a.val φ,
      fun s : {s : Roots H // s ≠ a} => restrict H s.val.val φ) := rfl

@[simp] theorem regroupTwo_apply (H : AbsForest n) (a b : Roots H) (hab : a ≠ b)
    (φ : Fin H.k → Label n) :
    regroupTwo H a b hab φ = ((restrict H a.val φ, restrict H b.val φ),
      fun s : ExceptTwo a b => restrict H s.val.val φ) := rfl

@[simp] theorem regroupTwo_coordinates (H : AbsForest n) (a b : Roots H) (hab : a ≠ b)
    (p : (LocalAssignment H a × LocalAssignment H b) × TwoSpectator H a b) :
    assignmentEquiv H ((regroupTwo H a b hab).symm p) =
      (twoPiEquiv (LocalAssignment H) a b hab).symm p := by
  exact (assignmentEquiv H).apply_symm_apply _

@[simp] theorem regroupOne_restrict_first (H : AbsForest n) (a : Roots H)
    (p : LocalAssignment H a × OneSpectator H a) :
    restrict H a.val ((regroupOne H a).symm p) = p.1 :=
  congrArg Prod.fst ((regroupOne H a).apply_symm_apply p)

@[simp] theorem regroupOne_restrict_rest (H : AbsForest n) (a : Roots H)
    (p : LocalAssignment H a × OneSpectator H a) (s : {s : Roots H // s ≠ a}) :
    restrict H s.val.val ((regroupOne H a).symm p) = p.2 s :=
  congrArg (fun q => q.2 s) ((regroupOne H a).apply_symm_apply p)

@[simp] theorem regroupTwo_restrict_first (H : AbsForest n) (a b : Roots H) (hab : a ≠ b)
    (p : (LocalAssignment H a × LocalAssignment H b) × TwoSpectator H a b) :
    restrict H a.val ((regroupTwo H a b hab).symm p) = p.1.1 :=
  congrArg (fun q => q.1.1) ((regroupTwo H a b hab).apply_symm_apply p)

@[simp] theorem regroupTwo_restrict_second (H : AbsForest n) (a b : Roots H) (hab : a ≠ b)
    (p : (LocalAssignment H a × LocalAssignment H b) × TwoSpectator H a b) :
    restrict H b.val ((regroupTwo H a b hab).symm p) = p.1.2 :=
  congrArg (fun q => q.1.2) ((regroupTwo H a b hab).apply_symm_apply p)

@[simp] theorem regroupTwo_restrict_rest (H : AbsForest n) (a b : Roots H) (hab : a ≠ b)
    (p : (LocalAssignment H a × LocalAssignment H b) × TwoSpectator H a b)
    (s : ExceptTwo a b) :
    restrict H s.val.val ((regroupTwo H a b hab).symm p) = p.2 s :=
  congrArg (fun q => q.2 s) ((regroupTwo H a b hab).apply_symm_apply p)

noncomputable def regroupOneHil (H : AbsForest n) (a : Roots H) :
    Hil (Fin H.k → Label n) ≃ₗᵢ[ℂ] Hil (LocalAssignment H a × OneSpectator H a) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (regroupOne H a)

noncomputable def regroupTwoHil (H : AbsForest n) (a b : Roots H) (hab : a ≠ b) :
    Hil (Fin H.k → Label n) ≃ₗᵢ[ℂ]
      Hil ((LocalAssignment H a × LocalAssignment H b) × TwoSpectator H a b) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (regroupTwo H a b hab)

@[simp] theorem regroupOneHil_apply (H : AbsForest n) (a : Roots H)
    (f : Hil (Fin H.k → Label n)) (p : LocalAssignment H a × OneSpectator H a) :
    regroupOneHil H a f p = f ((regroupOne H a).symm p) := rfl

@[simp] theorem regroupTwoHil_apply (H : AbsForest n) (a b : Roots H) (hab : a ≠ b)
    (f : Hil (Fin H.k → Label n))
    (p : (LocalAssignment H a × LocalAssignment H b) × TwoSpectator H a b) :
    regroupTwoHil H a b hab f p = f ((regroupTwo H a b hab).symm p) := rfl

theorem muRef_regroupTwo (l : ℕ) (G : WeldedInstance n) (H : AbsForest n)
    (hH : H.IsValid) (a b : Roots H) (hab : a ≠ b)
    (p : (LocalAssignment H a × LocalAssignment H b) × TwoSpectator H a b) :
    H.muRef l G ((regroupTwo H a b hab).symm p) =
      ((componentForest H a.val).muRef l G p.1.1 *
        (componentForest H b.val).muRef l G p.1.2) *
          ∏ s : ExceptTwo a b, (componentForest H s.val.val).muRef l G (p.2 s) := by
  rw [muRef_eq_product_coordinates l G H hH, regroupTwo_coordinates]
  exact twoPiEquiv_prod (LocalAssignment H)
    (fun s => (componentForest H s.val).muRef l G) a b hab p

theorem muRef_regroupOne (l : ℕ) (G : WeldedInstance n) (H : AbsForest n)
    (hH : H.IsValid) (a : Roots H) (p : LocalAssignment H a × OneSpectator H a) :
    H.muRef l G ((regroupOne H a).symm p) =
      (componentForest H a.val).muRef l G p.1 *
        ∏ s : {s : Roots H // s ≠ a}, (componentForest H s.val.val).muRef l G (p.2 s) := by
  calc
    _ = ∏ s : Roots H, (componentForest H s.val).muRef l G
        (restrict H s.val ((regroupOne H a).symm p)) :=
      by simpa only [assignmentEquiv_restrict] using
        muRef_eq_product_coordinates l G H hH ((regroupOne H a).symm p)
    _ = (componentForest H a.val).muRef l G (restrict H a.val ((regroupOne H a).symm p)) *
        ∏ s : {s : Roots H // s ≠ a}, (componentForest H s.val.val).muRef l G
          (restrict H s.val.val ((regroupOne H a).symm p)) := prod_one _ a
    _ = _ := by simp only [regroupOne_restrict_first, regroupOne_restrict_rest]

noncomputable def productAmplitude (H : AbsForest n)
    (f : (s : Roots H) → Hil (LocalAssignment H s)) : Hil (Fin H.k → Label n) :=
  WithLp.toLp 2 (fun φ => ∏ s : Roots H, f s (restrict H s.val φ))

noncomputable def spectatorAmplitude (H : AbsForest n) (a b : Roots H)
    (f : (s : Roots H) → Hil (LocalAssignment H s)) : Hil (TwoSpectator H a b) :=
  WithLp.toLp 2 (fun ψ => ∏ s : ExceptTwo a b, f s.val (ψ s))

noncomputable def oneSpectatorAmplitude (H : AbsForest n) (a : Roots H)
    (f : (s : Roots H) → Hil (LocalAssignment H s)) : Hil (OneSpectator H a) :=
  WithLp.toLp 2 (fun ψ => ∏ s : {s : Roots H // s ≠ a}, f s.val (ψ s))

theorem regroupOne_productAmplitude (H : AbsForest n) (a : Roots H)
    (f : (s : Roots H) → Hil (LocalAssignment H s)) :
    regroupOneHil H a (productAmplitude H f) =
      ketTensor (f a) (oneSpectatorAmplitude H a f) := by
  ext p
  rw [regroupOneHil_apply, ketTensor_apply]
  change (∏ s, f s (restrict H s.val ((regroupOne H a).symm p))) = _
  rw [prod_one _ a]
  simp only [regroupOne_restrict_first, regroupOne_restrict_rest]
  rfl

theorem regroupTwo_productAmplitude (H : AbsForest n) (a b : Roots H) (hab : a ≠ b)
    (f : (s : Roots H) → Hil (LocalAssignment H s)) :
    regroupTwoHil H a b hab (productAmplitude H f) =
      ketTensor (ketTensor (f a) (f b)) (spectatorAmplitude H a b f) := by
  ext p
  rw [regroupTwoHil_apply, ketTensor_apply, ketTensor_apply]
  change (∏ s, f s (assignmentEquiv H ((regroupTwo H a b hab).symm p) s)) = _
  rw [regroupTwo_coordinates]
  exact twoPiEquiv_prod (LocalAssignment H) (fun s x => f s x) a b hab p

end WeldedPath.Supplement.ComponentForest

end

-- Solutions.WeldedPathCoefficientStability
section

namespace WeldedPath.CoefficientStability

open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

theorem norm_sum_sq_le_card_sum {ι : Type*} [Fintype ι] (v : ι → E) :
    ‖∑ i, v i‖ ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ i, ‖v i‖ ^ 2 := by
  have hs := norm_sum_le (Finset.univ : Finset ι) v
  have hsq : ‖∑ i, v i‖ ^ 2 ≤ (∑ i, ‖v i‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg fun i _ => norm_nonneg _)).mpr hs
  exact hsq.trans (by simpa using
    (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => ‖v i‖)))

/-- Components lying in the discarded kernel have zero inner product with a minimal
representative. Removing those components cannot decrease the norm of its collision projection. -/
theorem collision_remove_kernel (K C : Submodule ℂ E) (f k r : E)
    (hf : f ∈ Kᗮ) (hk : k ∈ K) (hkC : k ∈ C)
    (hdec : C.starProjection f = k + r) :
    ‖C.starProjection f‖ ^ 2 ≤ ‖r‖ ^ 2 := by
  have horth : inner ℂ (C.starProjection f) k = 0 := by
    rw [C.inner_starProjection_left_eq_right,
      C.starProjection_eq_self_iff.mpr hkC]
    exact (K.mem_orthogonal' f).mp hf k hk
  have hneg : inner ℂ (C.starProjection f) (-k) = 0 := by
    simp only [inner_neg_right, horth, neg_zero]
  have hpy := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (C.starProjection f) (-k) hneg
  have he : C.starProjection f + -k = r := by rw [hdec]; abel
  rw [he, norm_neg] at hpy
  nlinarith [sq_nonneg ‖k‖]

/-- The collision estimate on arbitrary coefficient combinations. Fixed collision
parts lie in the discarded kernel; free parts are bounded separately, and their
energy is controlled by the orthogonal coefficient decomposition. -/
theorem collision_from_decomposition {ι : Type*} [Fintype ι]
    (K C : Submodule ℂ E) (f : E) (hf : f ∈ Kᗮ)
    (v k r : ι → E) (ε : ℝ) (hε : 0 ≤ ε)
    (hdec : C.starProjection f = (∑ i, k i) + ∑ i, r i)
    (hk : ∀ i, k i ∈ K) (hkC : ∀ i, k i ∈ C)
    (hr : ∀ i, ‖r i‖ ^ 2 ≤ ε * ‖v i‖ ^ 2)
    (henergy : (∑ i, ‖v i‖ ^ 2) ≤ ‖f‖ ^ 2) :
    ‖C.starProjection f‖ ^ 2 ≤ (Fintype.card ι : ℝ) * ε * ‖f‖ ^ 2 := by
  calc
    _ ≤ ‖∑ i, r i‖ ^ 2 := collision_remove_kernel K C f _ _ hf
      (K.sum_mem fun i _ => hk i) (C.sum_mem fun i _ => hkC i) hdec
    _ ≤ (Fintype.card ι : ℝ) * ∑ i, ‖r i‖ ^ 2 := norm_sum_sq_le_card_sum r
    _ ≤ (Fintype.card ι : ℝ) * (ε * ∑ i, ‖v i‖ ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => hr i
    _ ≤ (Fintype.card ι : ℝ) * (ε * ‖f‖ ^ 2) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left henergy hε) (by positivity)
    _ = _ := by ring

theorem projection_injective_on_minimal (S R : Submodule ℂ E) {f g : E}
    (hfS : f ∈ S) (hgS : g ∈ S)
    (hf : f ∈ (S ⊓ Rᗮ)ᗮ) (hg : g ∈ (S ⊓ Rᗮ)ᗮ)
    (he : R.starProjection f = R.starProjection g) : f = g := by
  have hzero : R.starProjection (f - g) = 0 := by rw [map_sub, he, sub_self]
  have hker : f - g ∈ S ⊓ Rᗮ :=
    ⟨S.sub_mem hfS hgS, R.starProjection_apply_eq_zero_iff.mp hzero⟩
  have horth : f - g ∈ (S ⊓ Rᗮ)ᗮ := (S ⊓ Rᗮ)ᗮ.sub_mem hf hg
  have heq : f - g = 0 := inner_self_eq_zero.mp
    (((S ⊓ Rᗮ).mem_orthogonal (f - g)).mp horth (f - g) hker)
  exact sub_eq_zero.mp heq

/-- The stable coefficient representative: remove the kernel of the injectivity
projection, then use the collision estimate to bound the representative's energy. -/
theorem stable_representative (S R : Submodule ℂ E)
    (hsmall : ∀ f ∈ S, f ∈ (S ⊓ Rᗮ)ᗮ →
      ‖Rᗮ.starProjection f‖ ^ 2 ≤ (1 / 2 : ℝ) * ‖f‖ ^ 2)
    (f₀ : E) (hf₀ : f₀ ∈ S) :
    ∃! f : E, f ∈ S ∧ f ∈ (S ⊓ Rᗮ)ᗮ ∧
      R.starProjection f = R.starProjection f₀ ∧
      ‖f‖ ^ 2 ≤ 2 * ‖R.starProjection f₀‖ ^ 2 := by
  let K : Submodule ℂ E := S ⊓ Rᗮ
  let f := f₀ - K.starProjection f₀
  have hk : K.starProjection f₀ ∈ K := K.starProjection_apply_mem _
  have hfS : f ∈ S := S.sub_mem hf₀ hk.1
  have hfK : f ∈ Kᗮ := K.sub_starProjection_mem_orthogonal f₀
  have hRf : R.starProjection f = R.starProjection f₀ := by
    dsimp [f]
    rw [map_sub, R.starProjection_apply_eq_zero_iff.mpr hk.2, sub_zero]
  have hbound : ‖f‖ ^ 2 ≤ 2 * ‖R.starProjection f₀‖ ^ 2 := by
    have hp := R.norm_sq_eq_add_norm_sq_starProjection f
    have hs := hsmall f hfS hfK
    rw [hRf] at hp
    linarith
  refine ⟨f, ⟨hfS, hfK, hRf, hbound⟩, ?_⟩
  intro g hg
  exact projection_injective_on_minimal S R hg.1 hfS hg.2.1 hfK (hg.2.2.1.trans hRf.symm)

end WeldedPath.CoefficientStability

end

-- Solutions.WeldedPathWeightedCoefficients
section

namespace WeldedPath.WeightedCoefficients

open scoped BigOperators
open HilbertSupport

variable {Ω D ι : Type*} [Fintype Ω] [Fintype ι]

/-- The coordinate subspace supported on an event. -/
def eventSpace (P : Ω → Prop) : Submodule ℂ (Hil Ω) where
  carrier := {f | ∀ ω, ¬ P ω → f ω = 0}
  zero_mem' := by simp
  add_mem' := by intro f g hf hg ω hω; simp [hf ω hω, hg ω hω]
  smul_mem' := by intro c f hf ω hω; simp [hf ω hω]

/-- The finite coordinate mask really is the orthogonal event projection. -/
theorem eventSpace_projection [DecidableEq Ω] (P : Ω → Prop) [DecidablePred P]
    (f : Hil Ω) : (eventSpace P).starProjection f = diagProj P f := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · intro ω hω
    simp [diagProj_apply, hω]
  · intro g hg
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    apply Finset.sum_eq_zero
    intro ω _
    by_cases hω : P ω
    · simp [diagProj_apply, hω]
    · simp [diagProj_apply, hω, hg ω hω]

theorem eventSpace_orthogonal [DecidableEq Ω] (P : Ω → Prop) :
    (eventSpace P)ᗮ = eventSpace (fun ω => ¬ P ω) := by
  classical
  ext f
  rw [← (eventSpace P).starProjection_apply_eq_zero_iff, eventSpace_projection,
    diagProj_zero_iff]
  change (∀ ω, P ω → f ω = 0) ↔ (∀ ω, ¬ ¬ P ω → f ω = 0)
  simp only [not_not]

/-- A union bound on squared coordinate-projection norms, valid for arbitrary amplitudes. -/
theorem event_union_norm_sq [DecidableEq Ω] (P : ι → Ω → Prop) (f : Hil Ω) :
    ‖(eventSpace (fun ω => ∃ i, P i ω)).starProjection f‖ ^ 2 ≤
      ∑ i, ‖(eventSpace (P i)).starProjection f‖ ^ 2 := by
  classical
  simp only [eventSpace_projection, EuclideanSpace.norm_sq_eq]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro ω _
  by_cases hω : ∃ i, P i ω
  · obtain ⟨i, hi⟩ := hω
    simp only [diagProj_apply, if_pos (show ∃ j, P j ω from ⟨i, hi⟩)]
    calc
      ‖f ω‖ ^ 2 = ‖if P i ω then f ω else 0‖ ^ 2 := by rw [if_pos hi]
      _ ≤ ∑ j, ‖if P j ω then f ω else 0‖ ^ 2 :=
        Finset.single_le_sum (fun j _ => sq_nonneg ‖if P j ω then f ω else 0‖)
          (Finset.mem_univ i)
  · simp only [diagProj_apply, if_neg hω, norm_zero, zero_pow (by decide : 2 ≠ 0)]
    exact Finset.sum_nonneg fun i _ => sq_nonneg _

/-- Lift a coefficient function into the Hilbert space with square-root density. -/
noncomputable def lift (μ : Ω → ℝ) (f : Ω → ℂ) : Hil Ω :=
  WithLp.toLp 2 (fun ω => (Real.sqrt (μ ω) : ℂ) * f ω)

theorem lift_norm_sq (μ : Ω → ℝ) (hμ : ∀ ω, 0 ≤ μ ω) (f : Ω → ℂ) :
    ‖lift μ f‖ ^ 2 = ∑ ω, μ ω * ‖f ω‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro ω _
  change ‖(Real.sqrt (μ ω) : ℂ) * f ω‖ ^ 2 = _
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (hμ ω)]

theorem masked_lift_norm_sq [DecidableEq Ω] (μ : Ω → ℝ) (hμ : ∀ ω, 0 ≤ μ ω)
    (P : Ω → Prop) [DecidablePred P] (f : Ω → ℂ) :
    ‖(eventSpace P).starProjection (lift μ f)‖ ^ 2 =
      ∑ ω, (if P ω then μ ω else 0) * ‖f ω‖ ^ 2 := by
  rw [eventSpace_projection, EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hω : P ω
  · simp only [diagProj_apply, if_pos hω]
    change ‖(Real.sqrt (μ ω) : ℂ) * f ω‖ ^ 2 = _
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (hμ ω)]
  · simp [diagProj_apply, hω]

theorem sum_by_data {R : Type*} [CommSemiring R] [DecidableEq D]
    (μ : Ω → R) (data : Ω → D) (h : D → R) :
    (∑ ω, μ ω * h (data ω)) =
      ∑ d ∈ Finset.univ.image data, h d * ∑ ω, if data ω = d then μ ω else 0 := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  simp [mul_ite, mul_comm, Finset.mem_image_of_mem data (Finset.mem_univ ω)]

/-- Conditional probability bounds control the energy of every coefficient
function measurable with respect to the fixed data, including arbitrary phases. -/
theorem conditional_event_bound [DecidableEq Ω] [DecidableEq D]
    (μ : Ω → ℝ) (hμ : ∀ ω, 0 ≤ μ ω) (data : Ω → D)
    (P : Ω → Prop) [DecidablePred P] (ε : ℝ)
    (hbound : ∀ d, (∑ ω, if data ω = d ∧ P ω then μ ω else 0) ≤
      ε * ∑ ω, if data ω = d then μ ω else 0)
    (h : D → ℂ) :
    ‖(eventSpace P).starProjection (lift μ (h ∘ data))‖ ^ 2 ≤
      ε * ‖lift μ (h ∘ data)‖ ^ 2 := by
  rw [masked_lift_norm_sq μ hμ, lift_norm_sq μ hμ]
  simp only [Function.comp_apply]
  rw [sum_by_data (fun ω => if P ω then μ ω else 0) data (fun d => ‖h d‖ ^ 2),
    sum_by_data μ data (fun d => ‖h d‖ ^ 2), Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d _
  have he : (∑ ω, if data ω = d then (if P ω then μ ω else 0) else 0) =
      ∑ ω, if data ω = d ∧ P ω then μ ω else 0 := by
    apply Finset.sum_congr rfl
    intro ω _
    split_ifs <;> simp_all
  rw [he]
  calc
    _ ≤ ‖h d‖ ^ 2 * (ε * ∑ ω, if data ω = d then μ ω else 0) :=
      mul_le_mul_of_nonneg_left (hbound d) (sq_nonneg _)
    _ = _ := by ring

end WeldedPath.WeightedCoefficients

end

-- Solutions.WeldedPathProductDecomposition
section

namespace WeldedPath.ProductDecomposition

open Classical HilbertSupport WeightedCoefficients
open scoped BigOperators

variable {X Y Z ι κ : Type*} [Fintype X] [Fintype Y] [Fintype ι] [Fintype κ]
  [DecidableEq X] [DecidableEq Y]

theorem masked_inner (P : X → Prop) (f g : Hil X) :
    inner ℂ ((eventSpace P).starProjection f) ((eventSpace P).starProjection g) =
      ∑ x, if P x then star (f x) * g x else 0 := by
  simp only [eventSpace_projection, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : P x <;> simp [diagProj_apply, hx, RCLike.inner_apply, mul_comm]

theorem tensor_collision_inner_left (a : X → Z) (b : Y → Z)
    (u w : Hil X) (v z : Hil Y)
    (h : ∀ y, inner ℂ ((eventSpace (fun x => a x = b y)).starProjection u)
      ((eventSpace (fun x => a x = b y)).starProjection w) = 0) :
    inner ℂ ((eventSpace (fun p : X × Y => a p.1 = b p.2)).starProjection (ketTensor u v))
      ((eventSpace (fun p : X × Y => a p.1 = b p.2)).starProjection (ketTensor w z)) = 0 := by
  rw [masked_inner, Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro y _
  have hh := h y
  rw [masked_inner] at hh
  calc
    _ = (star (v y) * z y) * ∑ x, if a x = b y then star (u x) * w x else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : a x = b y <;> simp only [ketTensor_apply, hx, if_true, if_false,
        star_mul, mul_zero]
      ring
    _ = 0 := by rw [hh, mul_zero]

theorem tensor_collision_inner_right (a : X → Z) (b : Y → Z)
    (u w : Hil X) (v z : Hil Y)
    (h : ∀ x, inner ℂ ((eventSpace (fun y => a x = b y)).starProjection v)
      ((eventSpace (fun y => a x = b y)).starProjection z) = 0) :
    inner ℂ ((eventSpace (fun p : X × Y => a p.1 = b p.2)).starProjection (ketTensor u v))
      ((eventSpace (fun p : X × Y => a p.1 = b p.2)).starProjection (ketTensor w z)) = 0 := by
  rw [masked_inner, Fintype.sum_prod_type]
  apply Finset.sum_eq_zero
  intro x _
  have hh := h x
  rw [masked_inner] at hh
  calc
    _ = (star (u x) * w x) * ∑ y, if a x = b y then star (v y) * z y else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : a x = b y <;> simp only [ketTensor_apply, hy, if_true, if_false,
        star_mul, mul_zero]
      ring
    _ = 0 := by rw [hh, mul_zero]

noncomputable def linearTensor (D : Hil X →ₗ[ℂ] Hil X) (E : Hil Y →ₗ[ℂ] Hil Y) :
    Hil (X × Y) →ₗ[ℂ] Hil (X × Y) :=
  (opTensor D.toContinuousLinearMap E.toContinuousLinearMap).toLinearMap

theorem linearTensor_ket (D : Hil X →ₗ[ℂ] Hil X) (E : Hil Y →ₗ[ℂ] Hil Y)
    (x : X) (y : Y) : linearTensor D E (ket (x,y)) = ketTensor (D (ket x)) (E (ket y)) :=
  opTensor_ket _ _ x y

theorem linearTensor_ket_pair (D : Hil X →ₗ[ℂ] Hil X) (E : Hil Y →ₗ[ℂ] Hil Y)
    (p : X × Y) : linearTensor D E (ket p) = ketTensor (D (ket p.1)) (E (ket p.2)) := by
  rcases p with ⟨x, y⟩
  exact linearTensor_ket D E x y

/-- Orthogonality in each tested-root fiber survives arbitrary entanglement
with the other component. There is no factor equal to the number of terms. -/
theorem product_collision_orthogonal
    (a : X → Z) (b : Y → Z)
    (D : ι → Hil X →ₗ[ℂ] Hil X) (E : κ → Hil Y →ₗ[ℂ] Hil Y)
    (hD : ∀ i j, i ≠ j → ∀ y f g,
      inner ℂ ((eventSpace (fun x => a x = b y)).starProjection (D i f))
        ((eventSpace (fun x => a x = b y)).starProjection (D j g)) = 0)
    (hE : ∀ i j, i ≠ j → ∀ x f g,
      inner ℂ ((eventSpace (fun y => a x = b y)).starProjection (E i f))
        ((eventSpace (fun y => a x = b y)).starProjection (E j g)) = 0)
    (i j : ι × κ) (hij : i ≠ j) (f g : Hil (X × Y)) :
    inner ℂ ((eventSpace (fun p : X × Y => a p.1 = b p.2)).starProjection
      (linearTensor (D i.1) (E i.2) f))
      ((eventSpace (fun p : X × Y => a p.1 = b p.2)).starProjection
        (linearTensor (D j.1) (E j.2) g)) = 0 := by
  have hzero (p q : X × Y) : inner ℂ
      ((eventSpace (fun r : X × Y => a r.1 = b r.2)).starProjection
        (ketTensor (D i.1 (ket p.1)) (E i.2 (ket p.2))))
      ((eventSpace (fun r : X × Y => a r.1 = b r.2)).starProjection
        (ketTensor (D j.1 (ket q.1)) (E j.2 (ket q.2)))) = 0 := by
    by_cases hleft : i.1 = j.1
    · have hright : i.2 ≠ j.2 := fun hh => hij (Prod.ext hleft hh)
      exact tensor_collision_inner_right a b _ _ _ _
        (fun x => hE i.2 j.2 hright x _ _)
    · exact tensor_collision_inner_left a b _ _ _ _
        (fun y => hD i.1 j.1 hleft y _ _)
  rw [← sum_basis f, ← sum_basis g]
  simp only [map_sum, map_smul, inner_sum, sum_inner, inner_smul_left, inner_smul_right,
    linearTensor_ket_pair, hzero, mul_zero, Finset.sum_const_zero]

end WeldedPath.ProductDecomposition

end

-- Solutions.WeldedPathConditionalCentering
section

namespace WeldedPath.WeightedCoefficients

open scoped BigOperators

variable {Ω D : Type*} [Fintype Ω] [DecidableEq D]

noncomputable def fiberMass (μ : Ω → ℝ) (data : Ω → D) (d : D) : ℝ :=
  ∑ ω, if data ω = d then μ ω else 0

noncomputable def fiberMoment (μ : Ω → ℝ) (data : Ω → D) (f : Ω → ℂ) (d : D) : ℂ :=
  ∑ ω, if data ω = d then (μ ω : ℂ) * f ω else 0

noncomputable def conditionalMean (μ : Ω → ℝ) (data : Ω → D) (f : Ω → ℂ) (d : D) : ℂ :=
  fiberMoment μ data f d / (fiberMass μ data d : ℂ)

theorem fiberMass_nonneg (μ : Ω → ℝ) (hμ : ∀ ω, 0 ≤ μ ω) (data : Ω → D) (d : D) :
    0 ≤ fiberMass μ data d := by
  apply Finset.sum_nonneg
  intro ω _
  split_ifs
  · exact hμ ω
  · rfl

theorem fiberMoment_eq_zero_of_mass_zero (μ : Ω → ℝ) (hμ : ∀ ω, 0 ≤ μ ω)
    (data : Ω → D) (f : Ω → ℂ) (d : D) (hz : fiberMass μ data d = 0) :
    fiberMoment μ data f d = 0 := by
  have hzero : ∀ ω, (if data ω = d then μ ω else 0) = 0 := by
    have hn : ∀ ω ∈ (Finset.univ : Finset Ω),
        0 ≤ (if data ω = d then μ ω else 0) := by
      intro ω _; split_ifs; exact hμ ω; rfl
    exact fun ω => (Finset.sum_eq_zero_iff_of_nonneg hn).mp hz ω (Finset.mem_univ ω)
  apply Finset.sum_eq_zero
  intro ω _
  by_cases hd : data ω = d
  · have he : μ ω = 0 := by simpa only [if_pos hd] using hzero ω
    simp [hd, he]
  · simp [hd]

/-- Subtracting a weighted conditional mean produces exactly zero conditional
mean, including fibers with zero reference mass. -/
theorem conditional_centered (μ : Ω → ℝ) (hμ : ∀ ω, 0 ≤ μ ω)
    (data : Ω → D) (f : Ω → ℂ) (d : D) :
    (∑ ω, if data ω = d then
      (μ ω : ℂ) * (f ω - conditionalMean μ data f d) else 0) = 0 := by
  have he : (∑ ω, if data ω = d then
      (μ ω : ℂ) * (f ω - conditionalMean μ data f d) else 0) =
      fiberMoment μ data f d -
        (fiberMass μ data d : ℂ) * conditionalMean μ data f d := by
    simp only [fiberMoment, fiberMass, Complex.ofReal_sum,
      Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro ω _
    split_ifs <;> simp [mul_sub]
  rw [he]
  by_cases hz : fiberMass μ data d = 0
  · simp [hz, fiberMoment_eq_zero_of_mass_zero μ hμ data f d hz]
  · have hzc : (fiberMass μ data d : ℂ) ≠ 0 := by exact_mod_cast hz
    simp only [conditionalMean]
    rw [mul_div_cancel₀ _ hzc, sub_self]

theorem inner_lift (μ : Ω → ℝ) (hμ : ∀ ω, 0 ≤ μ ω) (f g : Ω → ℂ) :
    inner ℂ (lift μ f) (lift μ g) = ∑ ω, (μ ω : ℂ) * star (f ω) * g ω := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  apply Finset.sum_congr rfl
  intro ω _
  change ((Real.sqrt (μ ω) : ℂ) * g ω) * star ((Real.sqrt (μ ω) : ℂ) * f ω) = _
  have hs : (Real.sqrt (μ ω) : ℂ) * (Real.sqrt (μ ω) : ℂ) = (μ ω : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt (hμ ω)
  simp only [star_mul, Complex.star_def, Complex.conj_ofReal]
  calc
    _ = ((Real.sqrt (μ ω) : ℂ) * (Real.sqrt (μ ω) : ℂ)) * star (f ω) * g ω := by
      simp only [Complex.star_def]
      ring
    _ = _ := by rw [hs]; rfl

/-- A centered coefficient is orthogonal to every coefficient depending only
on the conditioning data. The square-root density is the same as in gVec. -/
theorem conditional_center_orthogonal (μ : Ω → ℝ) (hμ : ∀ ω, 0 ≤ μ ω)
    (data : Ω → D) (f : Ω → ℂ) (h : D → ℂ) :
    inner ℂ (lift μ (h ∘ data))
      (lift μ (fun ω => f ω - conditionalMean μ data f (data ω))) = 0 := by
  rw [inner_lift μ hμ]
  simp only [Function.comp_apply]
  calc
    _ = ∑ ω, ((μ ω : ℂ) * (f ω - conditionalMean μ data f (data ω))) * star (h (data ω)) := by
      apply Finset.sum_congr rfl
      intro ω _
      ring
    _ = ∑ d ∈ Finset.univ.image data, star (h d) *
        ∑ ω, if data ω = d then
          (μ ω : ℂ) * (f ω - conditionalMean μ data f (data ω)) else 0 :=
      sum_by_data _ data (fun d => star (h d))
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro d _
      have hz : (∑ ω, if data ω = d then
          (μ ω : ℂ) * (f ω - conditionalMean μ data f (data ω)) else 0) = 0 := by
        calc
          _ = ∑ ω, if data ω = d then
              (μ ω : ℂ) * (f ω - conditionalMean μ data f d) else 0 := by
            apply Finset.sum_congr rfl
            intro ω _
            by_cases hd : data ω = d <;> simp [hd]
          _ = 0 := conditional_centered μ hμ data f d
      rw [hz, mul_zero]

end WeldedPath.WeightedCoefficients

end

-- Solutions.WeldedPathLocalCoefficientSpace
section

namespace WeldedPath.WeightedCoefficients

variable {Ω D : Type*} [Fintype Ω]

/-- The linear map from data-measurable coefficient functions into their
square-root-density Hilbert representation. -/
noncomputable def coefficientMap (μ : Ω → ℝ) (data : Ω → D) :
    (D → ℂ) →ₗ[ℂ] Hil Ω where
  toFun h := lift μ (h ∘ data)
  map_add' h g := by
    ext ω
    change (Real.sqrt (μ ω) : ℂ) * (h (data ω) + g (data ω)) =
      (Real.sqrt (μ ω) : ℂ) * h (data ω) + (Real.sqrt (μ ω) : ℂ) * g (data ω)
    ring
  map_smul' c h := by
    ext ω
    change (Real.sqrt (μ ω) : ℂ) * (c * h (data ω)) =
      c * ((Real.sqrt (μ ω) : ℂ) * h (data ω))
    ring

noncomputable def dataSpace (μ : Ω → ℝ) (data : Ω → D) : Submodule ℂ (Hil Ω) :=
  LinearMap.range (coefficientMap μ data)

theorem mem_dataSpace (μ : Ω → ℝ) (data : Ω → D) (f : Hil Ω) :
    f ∈ dataSpace μ data ↔ ∃ h : D → ℂ, lift μ (h ∘ data) = f := Iff.rfl

theorem lift_mem_dataSpace (μ : Ω → ℝ) (data : Ω → D) (h : D → ℂ) :
    lift μ (h ∘ data) ∈ dataSpace μ data := ⟨h, rfl⟩

theorem inner_zero_on_dataSpace (μ : Ω → ℝ) (data : Ω → D) (r : Hil Ω)
    (horth : ∀ h : D → ℂ, inner ℂ (lift μ (h ∘ data)) r = 0) :
    r ∈ (dataSpace μ data)ᗮ := by
  intro f hf
  obtain ⟨h, rfl⟩ := (mem_dataSpace μ data f).mp hf
  exact horth h

end WeldedPath.WeightedCoefficients

namespace WeldedPath.Supplement

noncomputable def localCoefficientSpace {n : ℕ} (H : AbsForest n)
    (μ : (Fin H.k → Label n) → ℝ) (v : Fin H.k) :
    Submodule ℂ (Hil (Fin H.k → Label n)) :=
  WeightedCoefficients.dataSpace μ (fun φ => H.Wfix φ v)

end WeldedPath.Supplement

end

-- Solutions.WeldedPathProductSpaces
section

namespace WeldedPath.ProductDecomposition

open Classical HilbertSupport WeightedCoefficients
open scoped BigOperators

variable {X Y ι κ A B : Type*} [Fintype X] [Fintype Y] [Fintype ι] [Fintype κ]
  [DecidableEq X] [DecidableEq Y]

noncomputable def column (f : Hil (X × Y)) (y : Y) : Hil X :=
  WithLp.toLp 2 (fun x => f (x,y))

noncomputable def row (f : Hil (X × Y)) (x : X) : Hil Y :=
  WithLp.toLp 2 (fun y => f (x,y))

noncomputable def rightAction (E : Hil Y →ₗ[ℂ] Hil Y) (f : Hil (X × Y)) : Hil (X × Y) :=
  WithLp.toLp 2 (fun p => E (row f p.1) p.2)

theorem linear_apply_basis (D : Hil X →ₗ[ℂ] Hil X) (f : Hil X) (x : X) :
    D f x = ∑ a, f a * D (ket a) x := by
  conv_lhs => rw [← sum_basis f]
  simp only [map_sum, map_smul, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply,
    smul_eq_mul]

theorem linearTensor_apply (D : Hil X →ₗ[ℂ] Hil X) (E : Hil Y →ₗ[ℂ] Hil Y)
    (f : Hil (X × Y)) (x : X) (y : Y) :
    linearTensor D E f (x,y) = ∑ a, ∑ b, f (a,b) * D (ket a) x * E (ket b) y := by
  conv_lhs => rw [← sum_basis f]
  simp only [map_sum, map_smul, linearTensor_ket_pair, WithLp.ofLp_sum, Finset.sum_apply,
    PiLp.smul_apply, smul_eq_mul, ketTensor_apply, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem rightAction_column (E : Hil Y →ₗ[ℂ] Hil Y) (f : Hil (X × Y)) (y : Y) :
    column (rightAction E f) y = ∑ b, E (ket b) y • column f b := by
  ext x
  change E (row f x) y = _
  rw [linear_apply_basis]
  simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro b _
  change f (x,b) * E (ket b) y = E (ket b) y * f (x,b)
  ring

theorem linearTensor_column (D : Hil X →ₗ[ℂ] Hil X) (E : Hil Y →ₗ[ℂ] Hil Y)
    (f : Hil (X × Y)) (x : X) (y : Y) :
    linearTensor D E f (x,y) = D (column (rightAction E f) y) x := by
  rw [linearTensor_apply, rightAction_column]
  simp only [map_sum, map_smul, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul]
  have hd (b : Y) : D (column f b) x = ∑ a, column f b a * D (ket a) x :=
    linear_apply_basis D (column f b) x
  simp_rw [hd]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  change f (a,b) * D (ket a) x * E (ket b) y = E (ket b) y * (f (a,b) * D (ket a) x)
  ring

/-- Independent linear resolutions of the two component spaces resolve all
joint coefficients, including entangled coefficients. -/
theorem product_resolution (S : Submodule ℂ (Hil X)) (T : Submodule ℂ (Hil Y))
    (D : ι → Hil X →ₗ[ℂ] Hil X) (E : κ → Hil Y →ₗ[ℂ] Hil Y)
    (hD : ∀ f ∈ S, (∑ i, D i f) = f) (hE : ∀ g ∈ T, (∑ j, E j g) = g)
    (f : Hil (X × Y)) (hcol : ∀ y, column f y ∈ S) (hrow : ∀ x, row f x ∈ T) :
    (∑ ij : ι × κ, linearTensor (D ij.1) (E ij.2) f) = f := by
  ext p
  rcases p with ⟨x,y⟩
  simp only [WithLp.ofLp_sum, Finset.sum_apply, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  have hi (j : κ) : (∑ i, linearTensor (D i) (E j) f (x,y)) = E j (row f x) y := by
    simp only [linearTensor_column]
    have hm : column (rightAction (E j) f) y ∈ S := by
      rw [rightAction_column]
      exact S.sum_mem (fun b _ => S.smul_mem _ (hcol b))
    have hh := congrArg (fun z : Hil X => z x) (hD _ hm)
    simpa only [WithLp.ofLp_sum, Finset.sum_apply, column, rightAction, PiLp.toLp_apply] using hh
  simp_rw [hi]
  have hh := congrArg (fun z : Hil Y => z y) (hE _ (hrow x))
  simpa only [WithLp.ofLp_sum, Finset.sum_apply, row, PiLp.toLp_apply] using hh

theorem tensor_lift (μ : X → ℝ) (ν : Y → ℝ) (hμ : ∀ x, 0 ≤ μ x)
    (a : X → ℂ) (b : Y → ℂ) :
    ketTensor (lift μ a) (lift ν b) =
      lift (fun p : X × Y => μ p.1 * ν p.2) (fun p => a p.1 * b p.2) := by
  ext p
  rcases p with ⟨x,y⟩
  change ((Real.sqrt (μ x) : ℂ) * a x) * ((Real.sqrt (ν y) : ℂ) * b y) =
    (Real.sqrt (μ x * ν y) : ℂ) * (a x * b y)
  rw [Real.sqrt_mul (hμ x), Complex.ofReal_mul]
  ring

theorem linearTensor_mem_dataSpace (μ : X → ℝ) (ν : Y → ℝ) (hμ : ∀ x, 0 ≤ μ x)
    (dataX : X → A) (dataY : Y → B)
    (D : Hil X →ₗ[ℂ] Hil X) (E : Hil Y →ₗ[ℂ] Hil Y)
    (hD : ∀ f, D f ∈ dataSpace μ dataX) (hE : ∀ g, E g ∈ dataSpace ν dataY)
    (f : Hil (X × Y)) :
    linearTensor D E f ∈ dataSpace (fun p : X × Y => μ p.1 * ν p.2)
      (fun p => (dataX p.1, dataY p.2)) := by
  rw [← sum_basis f, map_sum]
  apply Submodule.sum_mem
  intro p _
  rw [map_smul]
  apply Submodule.smul_mem
  rw [linearTensor_ket_pair]
  obtain ⟨a, ha⟩ := (mem_dataSpace μ dataX _).mp (hD (ket p.1))
  obtain ⟨b, hb⟩ := (mem_dataSpace ν dataY _).mp (hE (ket p.2))
  rw [← ha, ← hb, tensor_lift μ ν hμ]
  exact lift_mem_dataSpace _ _ (fun d : A × B => a d.1 * b d.2)

end WeldedPath.ProductDecomposition

end

-- Solutions.WeldedPathOrthogonalCollision
section

namespace WeldedPath.CoefficientStability

open scoped BigOperators

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [Fintype ι]

theorem norm_sum_sq_orthogonal (v : ι → E)
    (horth : ∀ i j, i ≠ j → inner ℂ (v i) (v j) = 0) :
    ‖∑ i, v i‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  classical
  have aux (s : Finset ι) : ‖∑ i ∈ s, v i‖ ^ 2 = ∑ i ∈ s, ‖v i‖ ^ 2 := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      have hz : inner ℂ (v i) (∑ j ∈ s, v j) = 0 := by
        rw [inner_sum]
        exact Finset.sum_eq_zero (fun j hj => horth i j (fun he => hi (he ▸ hj)))
      have hp := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (v i) (∑j∈s,v j) hz
      simpa only [← pow_two, ih] using hp
  exact aux Finset.univ

/-- In a collision-orthogonal decomposition, fixed collision pieces vanish
individually by minimality. The remaining estimates add without a term-count
loss, which is essential for collisions between distinct graph components. -/
theorem orthogonal_collision_bound (K C : Submodule ℂ E)
    (f : E) (hf : f ∈ Kᗮ) (v : ι → E) (hdec : (∑ i, v i) = f)
    (horth : ∀ i j, i ≠ j →
      inner ℂ (C.starProjection (v i)) (C.starProjection (v j)) = 0)
    (fixed : ι → Prop)
    (hfixed : ∀ i, fixed i → C.starProjection (v i) ∈ K)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hfree : ∀ i, ¬fixed i → ‖C.starProjection (v i)‖ ^ 2 ≤ ε * ‖v i‖ ^ 2)
    (henergy : (∑ i, ‖v i‖ ^ 2) ≤ ‖f‖ ^ 2) :
    ‖C.starProjection f‖ ^ 2 ≤ ε * ‖f‖ ^ 2 := by
  classical
  have hzero (i : ι) (hi : fixed i) : C.starProjection (v i) = 0 := by
    have hz : inner ℂ (C.starProjection f) (C.starProjection (v i)) = 0 := by
      rw [C.inner_starProjection_left_eq_right,
        C.starProjection_eq_self_iff.mpr (C.starProjection_apply_mem _)]
      exact (K.mem_orthogonal' f).mp hf _ (hfixed i hi)
    rw [← hdec, map_sum, sum_inner] at hz
    have he : (∑ j, inner ℂ (C.starProjection (v j)) (C.starProjection (v i))) =
        inner ℂ (C.starProjection (v i)) (C.starProjection (v i)) := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        exact horth j i hji
      · simp
    rw [he] at hz
    exact inner_self_eq_zero.mp hz
  calc
    ‖C.starProjection f‖ ^ 2 = ∑ i, ‖C.starProjection (v i)‖ ^ 2 := by
      rw [← hdec, map_sum]
      exact norm_sum_sq_orthogonal _ horth
    _ ≤ ∑ i, ε * ‖v i‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : fixed i
      · rw [hzero i hi, norm_zero, zero_pow (by decide : 2 ≠ 0)]
        exact mul_nonneg hε (sq_nonneg _)
      · exact hfree i hi
    _ = ε * ∑ i, ‖v i‖ ^ 2 := (Finset.mul_sum _ _ _).symm
    _ ≤ ε * ‖f‖ ^ 2 := mul_le_mul_of_nonneg_left henergy hε

end WeldedPath.CoefficientStability

end

-- Solutions.WeldedPathProductCoefficientSpace
section

namespace WeldedPath.ProductDecomposition

open Classical HilbertSupport WeightedCoefficients CoefficientStability
open scoped BigOperators

variable {X Y A B ι κ : Type*} [Fintype X] [Fintype Y] [Fintype ι] [Fintype κ]
  [DecidableEq X] [DecidableEq Y]

noncomputable def columnMap (y : Y) : Hil (X × Y) →ₗ[ℂ] Hil X where
  toFun f := column f y
  map_add' _ _ := by ext x; rfl
  map_smul' _ _ := by ext x; rfl

noncomputable def rowMap (x : X) : Hil (X × Y) →ₗ[ℂ] Hil Y where
  toFun f := row f x
  map_add' _ _ := by ext y; rfl
  map_smul' _ _ := by ext y; rfl

noncomputable def jointSpace (μ : X → ℝ) (ν : Y → ℝ)
    (dataX : ι → X → A) (dataY : κ → Y → B) : Submodule ℂ (Hil (X × Y)) :=
  ⨆ ij : ι × κ, dataSpace (fun p : X × Y => μ p.1 * ν p.2)
    (fun p => (dataX ij.1 p.1, dataY ij.2 p.2))

theorem dataSpace_column (μ : X → ℝ) (ν : Y → ℝ) (hμ : ∀ x, 0 ≤ μ x)
    (dataX : X → A) (dataY : Y → B) (f : Hil (X × Y))
    (hf : f ∈ dataSpace (fun p : X × Y => μ p.1 * ν p.2)
      (fun p => (dataX p.1, dataY p.2))) (y : Y) :
    column f y ∈ dataSpace μ dataX := by
  obtain ⟨h, rfl⟩ := (mem_dataSpace _ _ f).mp hf
  apply (mem_dataSpace μ dataX _).mpr
  refine ⟨fun a => (Real.sqrt (ν y) : ℂ) * h (a, dataY y), ?_⟩
  ext x
  change (Real.sqrt (μ x) : ℂ) * ((Real.sqrt (ν y) : ℂ) * h (dataX x, dataY y)) =
    (Real.sqrt (μ x * ν y) : ℂ) * h (dataX x, dataY y)
  rw [Real.sqrt_mul (hμ x), Complex.ofReal_mul]
  ring

theorem dataSpace_row (μ : X → ℝ) (ν : Y → ℝ) (hμ : ∀ x, 0 ≤ μ x)
    (dataX : X → A) (dataY : Y → B) (f : Hil (X × Y))
    (hf : f ∈ dataSpace (fun p : X × Y => μ p.1 * ν p.2)
      (fun p => (dataX p.1, dataY p.2))) (x : X) :
    row f x ∈ dataSpace ν dataY := by
  obtain ⟨h, rfl⟩ := (mem_dataSpace _ _ f).mp hf
  apply (mem_dataSpace ν dataY _).mpr
  refine ⟨fun b => (Real.sqrt (μ x) : ℂ) * h (dataX x, b), ?_⟩
  ext y
  change (Real.sqrt (ν y) : ℂ) * ((Real.sqrt (μ x) : ℂ) * h (dataX x, dataY y)) =
    (Real.sqrt (μ x * ν y) : ℂ) * h (dataX x, dataY y)
  rw [Real.sqrt_mul (hμ x), Complex.ofReal_mul]
  ring

theorem jointSpace_column (μ : X → ℝ) (ν : Y → ℝ) (hμ : ∀ x, 0 ≤ μ x)
    (dataX : ι → X → A) (dataY : κ → Y → B)
    (f : Hil (X × Y)) (hf : f ∈ jointSpace μ ν dataX dataY) (y : Y) :
    column f y ∈ ⨆ i, dataSpace μ (dataX i) := by
  have hle : jointSpace μ ν dataX dataY ≤
      (⨆ i, dataSpace μ (dataX i)).comap (columnMap y) := by
    apply iSup_le
    intro ij g hg
    exact (le_iSup (fun i => dataSpace μ (dataX i)) ij.1)
      (dataSpace_column μ ν hμ _ _ g hg y)
  exact hle hf

theorem jointSpace_row (μ : X → ℝ) (ν : Y → ℝ) (hμ : ∀ x, 0 ≤ μ x)
    (dataX : ι → X → A) (dataY : κ → Y → B)
    (f : Hil (X × Y)) (hf : f ∈ jointSpace μ ν dataX dataY) (x : X) :
    row f x ∈ ⨆ j, dataSpace ν (dataY j) := by
  have hle : jointSpace μ ν dataX dataY ≤
      (⨆ j, dataSpace ν (dataY j)).comap (rowMap x) := by
    apply iSup_le
    intro ij g hg
    exact (le_iSup (fun j => dataSpace ν (dataY j)) ij.2)
      (dataSpace_row μ ν hμ _ _ g hg x)
  exact hle hf

theorem linearTensor_support_left (D : Hil X →ₗ[ℂ] Hil X) (E : Hil Y →ₗ[ℂ] Hil Y)
    (P : X → Prop) (hD : ∀ f x, ¬P x → D f x = 0)
    (f : Hil (X × Y)) (x : X) (y : Y) (hx : ¬P x) :
    linearTensor D E f (x,y) = 0 := by
  rw [linearTensor_column]
  exact hD _ x hx

theorem linearTensor_support_right (D : Hil X →ₗ[ℂ] Hil X) (E : Hil Y →ₗ[ℂ] Hil Y)
    (P : Y → Prop) (hE : ∀ g y, ¬P y → E g y = 0)
    (f : Hil (X × Y)) (x : X) (y : Y) (hy : ¬P y) :
    linearTensor D E f (x,y) = 0 := by
  rw [linearTensor_apply]
  simp only [hE _ y hy, mul_zero, Finset.sum_const_zero]

theorem event_true (f : Hil X) : (eventSpace (fun _ : X => True)).starProjection f = f := by
  ext x
  simp [eventSpace_projection, diagProj_apply]

theorem product_orthogonal
    (D : ι → Hil X →ₗ[ℂ] Hil X) (E : κ → Hil Y →ₗ[ℂ] Hil Y)
    (hD : ∀ i j, i ≠ j → ∀ f g, inner ℂ (D i f) (D j g) = 0)
    (hE : ∀ i j, i ≠ j → ∀ f g, inner ℂ (E i f) (E j g) = 0)
    (i j : ι × κ) (hij : i ≠ j) (f g : Hil (X × Y)) :
    inner ℂ (linearTensor (D i.1) (E i.2) f) (linearTensor (D j.1) (E j.2) g) = 0 := by
  have h := product_collision_orthogonal (fun _ : X => ()) (fun _ : Y => ()) D E
    (fun i j hij y f g => by simpa only [event_true] using hD i j hij f g)
    (fun i j hij x f g => by simpa only [event_true] using hE i j hij f g)
    i j hij f g
  simpa only [event_true] using h

end WeldedPath.ProductDecomposition

end

-- Solutions.WeldedPathProductPointBound
section

namespace WeldedPath.ProductDecomposition

open Classical HilbertSupport WeightedCoefficients
open scoped BigOperators

variable {X Y A B Z : Type*} [Fintype X] [Fintype Y]
  [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B]

/-- A conditional point bound in one independent component controls a
cross-component coincidence, even for arbitrary joint fixed-data coefficients. -/
theorem product_point_fiber_bound
    (μ : X → ℝ) (ν : Y → ℝ) (hν : ∀ y, 0 ≤ ν y)
    (dataX : X → A) (dataY : Y → B) (a : X → Z) (b : Y → Z) (Free : X → Prop)
    (ε : ℝ)
    (hcap : ∀ d z, (∑ x, if dataX x = d ∧ Free x ∧ a x = z then μ x else 0) ≤
      ε * ∑ x, if dataX x = d then μ x else 0)
    (d : A × B) :
    (∑ p : X × Y, if (dataX p.1, dataY p.2) = d ∧
      (Free p.1 ∧ a p.1 = b p.2) then μ p.1 * ν p.2 else 0) ≤
      ε * ∑ p : X × Y, if (dataX p.1, dataY p.2) = d then μ p.1 * ν p.2 else 0 := by
  rcases d with ⟨d,e⟩
  simp only [Fintype.sum_prod_type, Prod.mk.injEq]
  rw [Finset.sum_comm, Finset.sum_comm (f := fun x y =>
    if dataX x = d ∧ dataY y = e then μ x * ν y else 0), Finset.mul_sum]
  apply Finset.sum_le_sum
  intro y _
  by_cases hy : dataY y = e
  · have hleft : (∑ x, if (dataX x = d ∧ dataY y = e) ∧ (Free x ∧ a x = b y)
        then μ x * ν y else 0) =
        (∑ x, if dataX x = d ∧ Free x ∧ a x = b y then μ x else 0) * ν y := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hd : dataX x = d <;> by_cases hf : Free x <;> by_cases hz : a x = b y <;>
        simp [hy, hd, hf, hz]
    have hright : (∑ x, if dataX x = d ∧ dataY y = e then μ x * ν y else 0) =
        (∑ x, if dataX x = d then μ x else 0) * ν y := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hd : dataX x = d <;> simp [hy, hd]
    rw [hleft, hright]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hcap d (b y)) (hν y)
  · simp [hy]

theorem product_point_energy_bound
    (μ : X → ℝ) (ν : Y → ℝ) (hμ : ∀ x, 0 ≤ μ x) (hν : ∀ y, 0 ≤ ν y)
    (dataX : X → A) (dataY : Y → B) (a : X → Z) (b : Y → Z) (Free : X → Prop)
    (ε : ℝ)
    (hcap : ∀ d z, (∑ x, if dataX x = d ∧ Free x ∧ a x = z then μ x else 0) ≤
      ε * ∑ x, if dataX x = d then μ x else 0)
    (f : Hil (X × Y))
    (hf : f ∈ dataSpace (fun p : X × Y => μ p.1 * ν p.2)
      (fun p => (dataX p.1, dataY p.2)))
    (hfree : ∀ x y, ¬Free x → f (x,y) = 0) :
    ‖(eventSpace (fun p : X × Y => a p.1 = b p.2)).starProjection f‖ ^ 2 ≤ ε * ‖f‖ ^ 2 := by
  obtain ⟨h, hh⟩ := (mem_dataSpace _ _ f).mp hf
  have he : (eventSpace (fun p : X × Y => a p.1 = b p.2)).starProjection f =
      (eventSpace (fun p : X × Y => Free p.1 ∧ a p.1 = b p.2)).starProjection f := by
    simp only [eventSpace_projection]
    ext p
    rcases p with ⟨x,y⟩
    by_cases hx : Free x
    · simp [diagProj_apply, hx]
    · simp [diagProj_apply, hx, hfree x y hx]
  rw [he, ← hh]
  exact conditional_event_bound (fun p : X × Y => μ p.1 * ν p.2)
    (fun p => mul_nonneg (hμ p.1) (hν p.2))
    (fun p => (dataX p.1, dataY p.2)) (fun p => Free p.1 ∧ a p.1 = b p.2)
    ε (product_point_fiber_bound μ ν hν dataX dataY a b Free ε hcap) h

end WeldedPath.ProductDecomposition

end

-- Solutions.WeldedPathProductPointRight
section

namespace WeldedPath.ProductDecomposition

open Classical HilbertSupport WeightedCoefficients
open scoped BigOperators

variable {X Y A B Z : Type*} [Fintype X] [Fintype Y]
  [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B]

theorem product_point_fiber_bound_right
    (μ : X → ℝ) (ν : Y → ℝ) (hμ : ∀ x, 0 ≤ μ x)
    (dataX : X → A) (dataY : Y → B) (a : X → Z) (b : Y → Z) (Free : Y → Prop)
    (ε : ℝ)
    (hcap : ∀ d z, (∑ y, if dataY y = d ∧ Free y ∧ b y = z then ν y else 0) ≤
      ε * ∑ y, if dataY y = d then ν y else 0)
    (d : A × B) :
    (∑ p : X × Y, if (dataX p.1, dataY p.2) = d ∧
      (Free p.2 ∧ a p.1 = b p.2) then μ p.1 * ν p.2 else 0) ≤
      ε * ∑ p : X × Y, if (dataX p.1, dataY p.2) = d then μ p.1 * ν p.2 else 0 := by
  have hh := product_point_fiber_bound ν μ hμ dataY dataX b a Free ε hcap (d.2,d.1)
  have hnum : (∑ p : Y × X, if (dataY p.1, dataX p.2) = (d.2,d.1) ∧
      (Free p.1 ∧ b p.1 = a p.2) then ν p.1 * μ p.2 else 0) =
      ∑ p : X × Y, if (dataX p.1, dataY p.2) = d ∧
        (Free p.2 ∧ a p.1 = b p.2) then μ p.1 * ν p.2 else 0 := by
    rw [← Equiv.sum_comp (Equiv.prodComm X Y)]
    apply Finset.sum_congr rfl
    rintro ⟨x,y⟩ _
    rcases d with ⟨d,e⟩
    have hzy : b y = a x ↔ a x = b y := eq_comm
    by_cases hd : dataX x = d <;> by_cases he : dataY y = e <;>
      by_cases hf : Free y <;> by_cases hz : a x = b y <;>
      simp [Equiv.prodComm_apply, hd, he, hf, hz, hzy, mul_comm]
  have hden : (∑ p : Y × X, if (dataY p.1, dataX p.2) = (d.2,d.1)
      then ν p.1 * μ p.2 else 0) =
      ∑ p : X × Y, if (dataX p.1, dataY p.2) = d then μ p.1 * ν p.2 else 0 := by
    rw [← Equiv.sum_comp (Equiv.prodComm X Y)]
    apply Finset.sum_congr rfl
    rintro ⟨x,y⟩ _
    rcases d with ⟨d,e⟩
    by_cases hd : dataX x = d <;> by_cases he : dataY y = e <;>
      simp [Equiv.prodComm_apply, hd, he, mul_comm]
  rw [hnum, hden] at hh
  exact hh

theorem product_point_energy_bound_right
    (μ : X → ℝ) (ν : Y → ℝ) (hμ : ∀ x, 0 ≤ μ x) (hν : ∀ y, 0 ≤ ν y)
    (dataX : X → A) (dataY : Y → B) (a : X → Z) (b : Y → Z) (Free : Y → Prop)
    (ε : ℝ)
    (hcap : ∀ d z, (∑ y, if dataY y = d ∧ Free y ∧ b y = z then ν y else 0) ≤
      ε * ∑ y, if dataY y = d then ν y else 0)
    (f : Hil (X × Y))
    (hf : f ∈ dataSpace (fun p : X × Y => μ p.1 * ν p.2)
      (fun p => (dataX p.1, dataY p.2)))
    (hfree : ∀ x y, ¬Free y → f (x,y) = 0) :
    ‖(eventSpace (fun p : X × Y => a p.1 = b p.2)).starProjection f‖ ^ 2 ≤ ε * ‖f‖ ^ 2 := by
  obtain ⟨h, hh⟩ := (mem_dataSpace _ _ f).mp hf
  have he : (eventSpace (fun p : X × Y => a p.1 = b p.2)).starProjection f =
      (eventSpace (fun p : X × Y => Free p.2 ∧ a p.1 = b p.2)).starProjection f := by
    simp only [eventSpace_projection]
    ext p
    rcases p with ⟨x,y⟩
    by_cases hy : Free y
    · simp [diagProj_apply, hy]
    · simp [diagProj_apply, hy, hfree x y hy]
  rw [he, ← hh]
  exact conditional_event_bound (fun p : X × Y => μ p.1 * ν p.2)
    (fun p => mul_nonneg (hμ p.1) (hν p.2))
    (fun p => (dataX p.1, dataY p.2)) (fun p => Free p.2 ∧ a p.1 = b p.2)
    ε (product_point_fiber_bound_right μ ν hμ dataX dataY a b Free ε hcap) h

end WeldedPath.ProductDecomposition

end

-- Solutions.WeldedPathComponentResolution
section

namespace WeldedPath.ProductDecomposition

open Classical HilbertSupport WeightedCoefficients CoefficientStability
open scoped BigOperators

variable {X Y A B Z ι κ : Type*} [Fintype X] [Fintype Y] [Fintype ι] [Fintype κ]
  [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B]

/-- The concrete rooted coefficient decomposition and point-cap information
needed to compare two independent components. Fixedness is an index property,
not an assignment-dependent mask of a centered term. -/
structure ComponentResolution (X ι A Z : Type*) [Fintype X] [Fintype ι]
    [DecidableEq X] [DecidableEq A] (ε : ℝ) where
  space : Submodule ℂ (Hil X)
  root : X → Z
  op : ι → Hil X →ₗ[ℂ] Hil X
  weight : ι → X → ℝ
  data : ι → X → A
  fixed : ι → Prop
  free : ι → X → Prop
  decode : ι → A → Z
  weight_nonneg : ∀ i x, 0 ≤ weight i x
  local_le : ∀ i, dataSpace (weight i) (data i) ≤ space
  range_mem : ∀ i f, op i f ∈ dataSpace (weight i) (data i)
  sum_apply : ∀ f ∈ space, (∑ i, op i f) = f
  orthogonal : ∀ i j, i ≠ j → ∀ f g, inner ℂ (op i f) (op j g) = 0
  fiber_orthogonal : ∀ i j, i ≠ j → ∀ z f g,
    inner ℂ ((eventSpace (fun x => root x = z)).starProjection (op i f))
      ((eventSpace (fun x => root x = z)).starProjection (op j g)) = 0
  free_support : ∀ i, ¬fixed i → ∀ f x, ¬free i x → op i f x = 0
  fixed_value : ∀ i, fixed i → ∀ f x, op i f x ≠ 0 → root x = decode i (data i x)
  point_cap : ∀ i d z,
    (∑ x, if data i x = d ∧ free i x ∧ root x = z then weight i x else 0) ≤
      ε * ∑ x, if data i x = d then weight i x else 0

noncomputable def tensorSpace (S : Submodule ℂ (Hil X)) (T : Submodule ℂ (Hil Y)) :
    Submodule ℂ (Hil (X × Y)) :=
  (⨅ y, S.comap (columnMap y)) ⊓ (⨅ x, T.comap (rowMap x))

theorem mem_tensorSpace (S : Submodule ℂ (Hil X)) (T : Submodule ℂ (Hil Y))
    (f : Hil (X × Y)) :
    f ∈ tensorSpace S T ↔ (∀ y, column f y ∈ S) ∧ (∀ x, row f x ∈ T) := by
  simp only [tensorSpace, Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap]
  rfl

theorem local_product_le_tensorSpace (μ : X → ℝ) (ν : Y → ℝ) (hμ : ∀ x, 0 ≤ μ x)
    (dataX : X → A) (dataY : Y → B) (S : Submodule ℂ (Hil X)) (T : Submodule ℂ (Hil Y))
    (hS : dataSpace μ dataX ≤ S) (hT : dataSpace ν dataY ≤ T) :
    dataSpace (fun p : X × Y => μ p.1 * ν p.2) (fun p => (dataX p.1, dataY p.2)) ≤
      tensorSpace S T := by
  intro f hf
  exact (mem_tensorSpace S T f).mpr
    ⟨fun y => hS (dataSpace_column μ ν hμ dataX dataY f hf y),
      fun x => hT (dataSpace_row μ ν hμ dataX dataY f hf x)⟩

theorem masked_mem_dataSpace_of_support (μ : X → ℝ) (data : X → A)
    (P : X → Prop) (Q : A → Prop) (f : Hil X) (hf : f ∈ dataSpace μ data)
    (hsupport : ∀ x, f x ≠ 0 → (P x ↔ Q (data x))) :
    (eventSpace P).starProjection f ∈ dataSpace μ data := by
  obtain ⟨h, hh⟩ := (mem_dataSpace μ data f).mp hf
  apply (mem_dataSpace μ data _).mpr
  refine ⟨fun d => if Q d then h d else 0, ?_⟩
  ext x
  rw [eventSpace_projection, diagProj_apply]
  change (Real.sqrt (μ x) : ℂ) * (if Q (data x) then h (data x) else 0) =
    if P x then f x else 0
  have hx : (Real.sqrt (μ x) : ℂ) * h (data x) = f x :=
    congrArg (fun z : Hil X => z x) hh
  by_cases hz : f x = 0
  · by_cases hp : P x <;> by_cases hq : Q (data x) <;> simp [hp, hq, hx, hz]
  · have he := hsupport x hz
    by_cases hp : P x <;> simp [hp, ← he, hx]

/-- Cross-component collision energy has the one-point constant, without
any product of stability constants or number of local summands. -/
theorem resolved_cross_collision_bound (ε : ℝ) (hε : 0 ≤ ε)
    (L : ComponentResolution X ι A Z ε) (R : ComponentResolution Y κ B Z ε)
    (Good : Submodule ℂ (Hil (X × Y)))
    (hbad : eventSpace (fun p : X × Y => L.root p.1 = R.root p.2) ≤ Goodᗮ)
    (f : Hil (X × Y)) (hf : f ∈ tensorSpace L.space R.space)
    (hminimal : f ∈ (tensorSpace L.space R.space ⊓ Goodᗮ)ᗮ) :
    ‖(eventSpace (fun p : X × Y => L.root p.1 = R.root p.2)).starProjection f‖ ^ 2 ≤
      ε * ‖f‖ ^ 2 := by
  let V : ι × κ → Hil (X × Y) := fun ij => linearTensor (L.op ij.1) (R.op ij.2) f
  have hsum : (∑ ij, V ij) = f := product_resolution L.space R.space L.op R.op
    L.sum_apply R.sum_apply f ((mem_tensorSpace _ _ f).mp hf).1 ((mem_tensorSpace _ _ f).mp hf).2
  have hlocal (ij : ι × κ) : V ij ∈ dataSpace
      (fun p : X × Y => L.weight ij.1 p.1 * R.weight ij.2 p.2)
      (fun p => (L.data ij.1 p.1, R.data ij.2 p.2)) :=
    linearTensor_mem_dataSpace _ _ (L.weight_nonneg ij.1) _ _ _ _
      (L.range_mem ij.1) (R.range_mem ij.2) f
  apply orthogonal_collision_bound (tensorSpace L.space R.space ⊓ Goodᗮ)
    (eventSpace (fun p : X × Y => L.root p.1 = R.root p.2)) f hminimal V hsum
    (fun i j hij => product_collision_orthogonal L.root R.root L.op R.op
      (fun i j hij y g h => L.fiber_orthogonal i j hij (R.root y) g h)
      (fun i j hij x g h => by
        have hh := R.fiber_orthogonal i j hij (L.root x) g h
        simpa only [eq_comm] using hh) i j hij f f)
    (fun ij => L.fixed ij.1 ∧ R.fixed ij.2) ?_ ε hε ?_ ?_
  · intro ij hij
    have hmasked : (eventSpace (fun p : X × Y => L.root p.1 = R.root p.2)).starProjection
        (V ij) ∈ dataSpace
          (fun p : X × Y => L.weight ij.1 p.1 * R.weight ij.2 p.2)
          (fun p => (L.data ij.1 p.1, R.data ij.2 p.2)) := by
      apply masked_mem_dataSpace_of_support _ _ _
        (fun d : A × B => L.decode ij.1 d.1 = R.decode ij.2 d.2) _ (hlocal ij)
      rintro ⟨x,y⟩ hxy
      have hx : L.root x = L.decode ij.1 (L.data ij.1 x) := by
        apply L.fixed_value ij.1 hij.1 (column (rightAction (R.op ij.2) f) y) x
        simpa only [V, linearTensor_column] using hxy
      have hy : R.root y = R.decode ij.2 (R.data ij.2 y) := by
        by_contra hn
        have hz : V ij (x,y) = 0 := linearTensor_support_right _ _
          (fun y => R.root y = R.decode ij.2 (R.data ij.2 y))
          (fun g y hne => by
            by_contra hng
            exact hne (R.fixed_value ij.2 hij.2 g y hng)) f x y hn
        exact hxy hz
      simp only [hx, hy]
    refine ⟨?_, hbad ((eventSpace (fun p : X × Y => L.root p.1 = R.root p.2)).starProjection_apply_mem (V ij))⟩
    exact local_product_le_tensorSpace _ _ (L.weight_nonneg ij.1) _ _ L.space R.space
      (L.local_le ij.1) (R.local_le ij.2) hmasked
  · intro ij hij
    by_cases hL : L.fixed ij.1
    · have hR : ¬R.fixed ij.2 := fun hR => hij ⟨hL,hR⟩
      exact product_point_energy_bound_right _ _ (L.weight_nonneg ij.1) (R.weight_nonneg ij.2)
        _ _ L.root R.root (R.free ij.2) ε (R.point_cap ij.2) _ (hlocal ij)
        (fun x y hy => linearTensor_support_right _ _ _ (R.free_support ij.2 hR) f x y hy)
    · exact product_point_energy_bound _ _ (L.weight_nonneg ij.1) (R.weight_nonneg ij.2)
        _ _ L.root R.root (L.free ij.1) ε (L.point_cap ij.1) _ (hlocal ij)
        (fun x y hx => linearTensor_support_left _ _ _ (L.free_support ij.1 hL) f x y hx)
  · rw [← hsum]
    exact le_of_eq (norm_sum_sq_orthogonal V (fun i j hij =>
      product_orthogonal L.op R.op L.orthogonal R.orthogonal i j hij f f)).symm

end WeldedPath.ProductDecomposition

end

-- Solutions.WeldedPathTensorSpan
section

namespace WeldedPath.ProductDecomposition

open Classical HilbertSupport WeightedCoefficients
open scoped BigOperators

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

theorem ketTensor_mem_tensorSpace (S : Submodule ℂ (Hil X)) (T : Submodule ℂ (Hil Y))
    (a : Hil X) (ha : a ∈ S) (b : Hil Y) (hb : b ∈ T) :
    ketTensor a b ∈ tensorSpace S T := by
  apply (mem_tensorSpace S T _).mpr
  constructor
  · intro y
    have he : column (ketTensor a b) y = b y • a := by
      ext x
      change a x * b y = b y * a x
      ring
    rw [he]
    exact S.smul_mem _ ha
  · intro x
    have he : row (ketTensor a b) x = a x • b := by
      ext y
      rfl
    rw [he]
    exact T.smul_mem _ hb

/-- The slice characterization is precisely the span of product
coefficients, so passing to tensorSpace does not enlarge the good coefficient
space. -/
theorem tensorSpace_eq_span (S : Submodule ℂ (Hil X)) (T : Submodule ℂ (Hil Y)) :
    tensorSpace S T = Submodule.span ℂ
      {v | ∃ a ∈ S, ∃ b ∈ T, v = ketTensor a b} := by
  apply le_antisymm
  · intro f hf
    let D := S.starProjection.toLinearMap
    let E := T.starProjection.toLinearMap
    have he : linearTensor D E f = f := by
      have hh := product_resolution S T (fun _ : Unit => D) (fun _ : Unit => E)
        (fun g hg => by simpa [D] using S.starProjection_eq_self_iff.mpr hg)
        (fun g hg => by simpa [E] using T.starProjection_eq_self_iff.mpr hg)
        f ((mem_tensorSpace S T f).mp hf).1 ((mem_tensorSpace S T f).mp hf).2
      simpa using hh
    rw [← he, ← sum_basis f, map_sum]
    apply Submodule.sum_mem
    intro p _
    rw [map_smul]
    apply Submodule.smul_mem
    rw [linearTensor_ket_pair]
    exact Submodule.subset_span
      ⟨D (ket p.1), S.starProjection_apply_mem _, E (ket p.2),
        T.starProjection_apply_mem _, rfl⟩
  · apply Submodule.span_le.mpr
    rintro v ⟨a, ha, b, hb, rfl⟩
    exact ketTensor_mem_tensorSpace S T a ha b hb

end WeldedPath.ProductDecomposition

end

-- Solutions.WeldedPathComponentProductSpace
section

namespace WeldedPath.Supplement.ComponentForest

open Classical QAlgorithms HilbertSupport ProductDecomposition
open scoped BigOperators

variable {n : ℕ}

@[simp] theorem regroupOne_label (H : AbsForest n) (a : Roots H)
    (p : LocalAssignment H a × OneSpectator H a) (i : Fin (H.comp a.val).card) :
    (regroupOne H a).symm p (vertexMap H a.val i) = p.1 i :=
  congrFun (regroupOne_restrict_first H a p) i

@[simp] theorem regroupTwo_label_first (H : AbsForest n) (a b : Roots H) (hab : a ≠ b)
    (p : (LocalAssignment H a × LocalAssignment H b) × TwoSpectator H a b)
    (i : Fin (H.comp a.val).card) :
    (regroupTwo H a b hab).symm p (vertexMap H a.val i) = p.1.1 i :=
  congrFun (regroupTwo_restrict_first H a b hab p) i

@[simp] theorem regroupTwo_label_second (H : AbsForest n) (a b : Roots H) (hab : a ≠ b)
    (p : (LocalAssignment H a × LocalAssignment H b) × TwoSpectator H a b)
    (i : Fin (H.comp b.val).card) :
    (regroupTwo H a b hab).symm p (vertexMap H b.val i) = p.1.2 i :=
  congrFun (regroupTwo_restrict_second H a b hab p) i

section TensorSpans

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

noncomputable def tensorLeftMap (x : Hil X) : Hil Y →ₗ[ℂ] Hil (X × Y) where
  toFun := ketTensor x
  map_add' u v := by
    ext p
    change x p.1 * (u p.2 + v p.2) = x p.1 * u p.2 + x p.1 * v p.2
    ring
  map_smul' c u := by
    ext p
    change x p.1 * (c * u p.2) = c * (x p.1 * u p.2)
    ring

noncomputable def tensorRightMap (y : Hil Y) : Hil X →ₗ[ℂ] Hil (X × Y) where
  toFun x := ketTensor x y
  map_add' u v := by
    ext p
    change (u p.1 + v p.1) * y p.2 = u p.1 * y p.2 + v p.1 * y p.2
    ring
  map_smul' c u := by
    ext p
    change (c * u p.1) * y p.2 = c * (u p.1 * y p.2)
    ring

theorem tensorSpace_spans (A : Set (Hil X)) (B : Set (Hil Y)) :
    tensorSpace (Submodule.span ℂ A) (Submodule.span ℂ B) =
      Submodule.span ℂ {v | ∃ a ∈ A, ∃ b ∈ B, v = ketTensor a b} := by
  let U := Submodule.span ℂ {v | ∃ a ∈ A, ∃ b ∈ B, v = ketTensor a b}
  have hA (b : Hil Y) (hb : b ∈ B) :
      Submodule.span ℂ A ≤ U.comap (tensorRightMap b) := by
    apply Submodule.span_le.mpr
    intro a ha
    exact Submodule.subset_span ⟨a, ha, b, hb, rfl⟩
  have hB (a : Hil X) (ha : a ∈ Submodule.span ℂ A) :
      Submodule.span ℂ B ≤ U.comap (tensorLeftMap a) := by
    apply Submodule.span_le.mpr
    intro b hb
    exact hA b hb ha
  apply le_antisymm
  · rw [tensorSpace_eq_span]
    apply Submodule.span_le.mpr
    rintro v ⟨a, ha, b, hb, rfl⟩
    exact hB a ha hb
  · apply Submodule.span_le.mpr
    rintro v ⟨a, ha, b, hb, rfl⟩
    exact ketTensor_mem_tensorSpace _ _ _ (Submodule.subset_span ha) _ (Submodule.subset_span hb)

theorem tensorSpace_span_right (S : Submodule ℂ (Hil X)) (B : Set (Hil Y)) :
    tensorSpace S (Submodule.span ℂ B) =
      Submodule.span ℂ {v | ∃ a ∈ S, ∃ b ∈ B, v = ketTensor a b} := by
  simpa only [Submodule.span_eq, SetLike.mem_coe] using tensorSpace_spans (S : Set (Hil X)) B

end TensorSpans

noncomputable def piAmplitude {I : Type*} [Fintype I] {X : I → Type*}
    [∀ i, Fintype (X i)] (f : (i : I) → Hil (X i)) : Hil ((i : I) → X i) :=
  WithLp.toLp 2 (fun z => ∏ i, f i (z i))

def piGenerators {I : Type*} [Fintype I] {X : I → Type*} [∀ i, Fintype (X i)]
    (S : (i : I) → Submodule ℂ (Hil (X i))) : Set (Hil ((i : I) → X i)) :=
  {v | ∃ f, (∀ i, f i ∈ S i) ∧ v = piAmplitude f}

noncomputable def piSpace {I : Type*} [Fintype I] {X : I → Type*}
    [∀ i, Fintype (X i)] (S : (i : I) → Submodule ℂ (Hil (X i))) :
    Submodule ℂ (Hil ((i : I) → X i)) := Submodule.span ℂ (piGenerators S)

def productGenerators (H : AbsForest n)
    (S : (s : Roots H) → Submodule ℂ (Hil (LocalAssignment H s))) :
    Set (Hil (Fin H.k → Label n)) :=
  {v | ∃ f, (∀ s, f s ∈ S s) ∧ v = productAmplitude H f}

/-- The source coefficient space generated by independent component
coefficients, written on the original assignment coordinates. -/
noncomputable def productSpace (H : AbsForest n)
    (S : (s : Roots H) → Submodule ℂ (Hil (LocalAssignment H s))) :
    Submodule ℂ (Hil (Fin H.k → Label n)) :=
  Submodule.span ℂ (productGenerators H S)

noncomputable def oneSpectatorSpace (H : AbsForest n)
    (S : (s : Roots H) → Submodule ℂ (Hil (LocalAssignment H s))) (a : Roots H) :
    Submodule ℂ (Hil (OneSpectator H a)) :=
  piSpace (fun s : {s : Roots H // s ≠ a} => S s.val)

noncomputable def twoSpectatorSpace (H : AbsForest n)
    (S : (s : Roots H) → Submodule ℂ (Hil (LocalAssignment H s))) (a b : Roots H) :
    Submodule ℂ (Hil (TwoSpectator H a b)) := piSpace (fun s : ExceptTwo a b => S s.val)

theorem regroupTwo_productSpace (H : AbsForest n)
    (S : (s : Roots H) → Submodule ℂ (Hil (LocalAssignment H s)))
    (a b : Roots H) (hab : a ≠ b) :
    (productSpace H S).map (regroupTwoHil H a b hab).toLinearMap =
      tensorSpace (tensorSpace (S a) (S b)) (twoSpectatorSpace H S a b) := by
  rw [productSpace, Submodule.map_span, tensorSpace_eq_span (S a) (S b),
    twoSpectatorSpace, piSpace, tensorSpace_spans]
  apply congrArg (Submodule.span ℂ)
  ext v
  constructor
  · rintro ⟨u, ⟨f, hf, rfl⟩, rfl⟩
    refine ⟨ketTensor (f a) (f b), ⟨f a, hf a, f b, hf b, rfl⟩,
      piAmplitude (fun s : ExceptTwo a b => f s.val),
      ⟨fun s => f s.val, fun s => hf s.val, rfl⟩, ?_⟩
    exact regroupTwo_productAmplitude H a b hab f
  · rintro ⟨u, ⟨fa, ha, fb, hb, rfl⟩, z, ⟨g, hg, rfl⟩, rfl⟩
    let f := (twoPiEquiv (fun s => Hil (LocalAssignment H s)) a b hab).symm ((fa, fb), g)
    have hfa : f a = fa := twoPiEquiv_symm_first _ a b hab _
    have hfb : f b = fb := twoPiEquiv_symm_second _ a b hab _
    have hfg (s : ExceptTwo a b) : f s.val = g s := twoPiEquiv_symm_rest _ a b hab _ s
    have hf (s : Roots H) : f s ∈ S s := by
      by_cases hsa : s = a
      · subst s; simpa only [hfa] using ha
      by_cases hsb : s = b
      · subst s; simpa only [hfb] using hb
      simpa only [hfg ⟨s, hsa, hsb⟩] using hg ⟨s, hsa, hsb⟩
    refine ⟨productAmplitude H f, ⟨f, hf, rfl⟩, ?_⟩
    change regroupTwoHil H a b hab (productAmplitude H f) = _
    rw [regroupTwo_productAmplitude, hfa, hfb]
    congr 1
    ext ψ
    change (∏ s : ExceptTwo a b, f s.val (ψ s)) = ∏ s : ExceptTwo a b, g s (ψ s)
    apply Finset.prod_congr rfl
    intro s _
    rw [hfg]

theorem regroupOne_productSpace (H : AbsForest n)
    (S : (s : Roots H) → Submodule ℂ (Hil (LocalAssignment H s))) (a : Roots H) :
    (productSpace H S).map (regroupOneHil H a).toLinearMap =
      tensorSpace (S a) (oneSpectatorSpace H S a) := by
  rw [productSpace, Submodule.map_span, oneSpectatorSpace, piSpace, tensorSpace_span_right]
  apply congrArg (Submodule.span ℂ)
  ext v
  constructor
  · rintro ⟨u, ⟨f, hf, rfl⟩, rfl⟩
    exact ⟨f a, hf a, piAmplitude (fun s : {s : Roots H // s ≠ a} => f s.val),
      ⟨fun s => f s.val, fun s => hf s.val, rfl⟩, regroupOne_productAmplitude H a f⟩
  · rintro ⟨fa, ha, z, ⟨g, hg, rfl⟩, rfl⟩
    let f := (Equiv.piSplitAt a (fun s => Hil (LocalAssignment H s))).symm (fa, g)
    have hfa : f a = fa := congrArg Prod.fst
      ((Equiv.piSplitAt a (fun s => Hil (LocalAssignment H s))).apply_symm_apply (fa, g))
    have hfg (s : {s : Roots H // s ≠ a}) : f s.val = g s := congrArg (fun z => z.2 s)
      ((Equiv.piSplitAt a (fun s => Hil (LocalAssignment H s))).apply_symm_apply (fa, g))
    have hf (s : Roots H) : f s ∈ S s := by
      by_cases hsa : s = a
      · subst s; simpa only [hfa] using ha
      simpa only [hfg ⟨s, hsa⟩] using hg ⟨s, hsa⟩
    refine ⟨productAmplitude H f, ⟨f, hf, rfl⟩, ?_⟩
    change regroupOneHil H a (productAmplitude H f) = _
    rw [regroupOne_productAmplitude, hfa]
    congr 1
    ext ψ
    change (∏ s : {s : Roots H // s ≠ a}, f s.val (ψ s)) =
      ∏ s : {s : Roots H // s ≠ a}, g s (ψ s)
    apply Finset.prod_congr rfl
    intro s _
    rw [hfg]

theorem regroupTwo_mem_iff (H : AbsForest n)
    (S : (s : Roots H) → Submodule ℂ (Hil (LocalAssignment H s)))
    (a b : Roots H) (hab : a ≠ b) (f : Hil (Fin H.k → Label n)) :
    regroupTwoHil H a b hab f ∈
      tensorSpace (tensorSpace (S a) (S b)) (twoSpectatorSpace H S a b) ↔
    f ∈ productSpace H S := by
  rw [← regroupTwo_productSpace H S a b hab]
  constructor
  · rintro ⟨g, hg, hgf⟩
    exact (regroupTwoHil H a b hab).injective hgf ▸ hg
  · intro hf
    exact ⟨f, hf, rfl⟩

theorem regroupOne_mem_iff (H : AbsForest n)
    (S : (s : Roots H) → Submodule ℂ (Hil (LocalAssignment H s)))
    (a : Roots H) (f : Hil (Fin H.k → Label n)) :
    regroupOneHil H a f ∈ tensorSpace (S a) (oneSpectatorSpace H S a) ↔
      f ∈ productSpace H S := by
  rw [← regroupOne_productSpace H S a]
  constructor
  · rintro ⟨g, hg, hgf⟩
    exact (regroupOneHil H a).injective hgf ▸ hg
  · intro hf
    exact ⟨f, hf, rfl⟩

end WeldedPath.Supplement.ComponentForest

end

-- Solutions.WeldedPathExitDegree
section

namespace WeldedPath.LoopProof

open WeldedInstance

lemma exit_col (n : ℕ) : col n (exitIdx n) = 2 * n + 1 := by
  simp [col, exitIdx]

lemma exit_parent_none (n : ℕ) : parent n (exitIdx n) = none := by
  have h1 : ¬ (IsVertex n (exitIdx n) ∧ 1 ≤ col n (exitIdx n) ∧
      col n (exitIdx n) ≤ n) := by rw [exit_col]; omega
  have h2 : ¬ (IsVertex n (exitIdx n) ∧ n + 1 ≤ col n (exitIdx n) ∧
      col n (exitIdx n) ≤ 2 * n) := by rw [exit_col]; omega
  rw [parent, if_neg h1, if_neg h2]

lemma root_size_bounds (n : ℕ) (hn : 2 ≤ n) :
    4 ≤ 2 ^ (n + 1) ∧ 2 ^ (n + 1) + 1 < numV n := by
  have hp : 4 ≤ 2 ^ (n + 1) := by
    calc
      4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  refine ⟨hp, ?_⟩
  unfold numV
  rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
  omega

lemma exit_isVertex (n : ℕ) (hn : 2 ≤ n) : IsVertex n (exitIdx n) := by
  have h := root_size_bounds n hn
  unfold IsVertex exitIdx
  omega

lemma exit_child_col (n : ℕ) (hn : 2 ≤ n) (j : ℕ) (hj : j ≤ 1) :
    col n (2 ^ (n + 1) + j) = 2 * n := by
  have hp := (root_size_bounds n hn).1
  have hlt : ¬2 ^ (n + 1) + j < 2 ^ (n + 1) - 1 := by omega
  have hdiff : 2 ^ (n + 1) + j - (2 ^ (n + 1) - 1) + 1 = j + 2 := by omega
  simp only [col, hlt, if_false, hdiff]
  have hjcases : j = 0 ∨ j = 1 := by omega
  rcases hjcases with rfl | rfl <;> norm_num <;> omega

lemma exit_child_parent (n : ℕ) (hn : 2 ≤ n) (j : ℕ) (hj : j ≤ 1) :
    parent n (2 ^ (n + 1) + j) = some (exitIdx n) := by
  have hv : IsVertex n (2 ^ (n + 1) + j) := by
    have h := (root_size_bounds n hn).2
    unfold IsVertex
    omega
  have hc := exit_child_col n hn j hj
  have hfirst : ¬(IsVertex n (2 ^ (n + 1) + j) ∧
      1 ≤ col n (2 ^ (n + 1) + j) ∧ col n (2 ^ (n + 1) + j) ≤ n) := by
    rw [hc]
    omega
  have hsecond : IsVertex n (2 ^ (n + 1) + j) ∧
      n + 1 ≤ col n (2 ^ (n + 1) + j) ∧ col n (2 ^ (n + 1) + j) ≤ 2 * n := by
    rw [hc]
    exact ⟨hv, by omega, le_refl _⟩
  rw [parent, if_neg hfirst, if_pos hsecond]
  simp [Nat.add_sub_cancel_left, show j / 2 = 0 by omega, exitIdx]

lemma exit_child_edge (n : ℕ) (hn : 2 ≤ n) (G : WeldedInstance n)
    (j : ℕ) (hj : j ≤ 1) : Edge.tree (2 ^ (n + 1) + j) ∈ G.edges := by
  apply Finset.mem_union_left
  apply Finset.mem_image.mpr
  refine ⟨2 ^ (n + 1) + j, ?_, rfl⟩
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · have h := (root_size_bounds n hn).2
    omega
  · rw [exit_child_parent n hn j hj]
    rfl

lemma exit_child_incident (n : ℕ) (hn : 2 ≤ n) (j : ℕ) (hj : j ≤ 1) :
    (Edge.tree (2 ^ (n + 1) + j)).Incident n (exitIdx n) := by
  right
  simp [Edge.head, exit_child_parent n hn j hj]

lemma exit_child_bEdge (n l : ℕ) (hn : 2 ≤ n) (hl : l ≤ n - 4)
    (G : WeldedInstance n) (j : ℕ) (hj : j ≤ 1) (hn4 : 4 ≤ n) :
    G.bEdge l (.tree (2 ^ (n + 1) + j)) = none := by
  have h : ¬(n - l ≤ col n (2 ^ (n + 1) + j) ∧
      col n (2 ^ (n + 1) + j) ≤ n + l) := by
    rw [exit_child_col n hn j hj]
    omega
  rw [WeldedInstance.bEdge, if_neg h]

lemma eAlpha_of_edge {n : ℕ} (G : WeldedInstance n) (hG : G.IsProperColoring)
    (e : Edge) (he : e ∈ G.edges) (v : ℕ) (hi : e.Incident n v) :
    G.eAlpha v (G.color e) = some e := by
  classical
  unfold WeldedInstance.eAlpha
  split_ifs with h
  · congr 1
    have hs := Classical.choose_spec h
    by_contra hne
    exact hG (Classical.choose h) hs.1 e he hne ⟨v, hs.2.2, hi⟩ hs.2.1
  · exact False.elim (h ⟨e, he, rfl, hi⟩)

lemma exit_incident_cases (n : ℕ) (hn : 2 ≤ n) (G : WeldedInstance n)
    (hG : G.IsValid) (e : Edge) (he : e ∈ G.edges) (hi : e.Incident n (exitIdx n)) :
    e = .tree (2 ^ (n + 1)) ∨ e = .tree (2 ^ (n + 1) + 1) := by
  classical
  cases e with
  | tree v =>
    have ht : v < numV n ∧ (parent n v).isSome := by
      simpa [WeldedInstance.edges, treeEdges, weldEdges] using he
    cases hp : parent n v with
    | none => simp [hp] at ht
    | some p =>
      have hne : v ≠ exitIdx n := by
        intro hv
        subst v
        rw [exit_parent_none] at hp
        contradiction
      have hvr : exitIdx n = p := by
        simpa [Edge.Incident, Edge.tail, Edge.head, hp, Ne.symm hne] using hi
      have hpar : parent n v = some (exitIdx n) := by simpa [hvr] using hp
      rcases parent_eq_exit_imp hpar with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
  | weld u w =>
    have hw : (u, w) ∈ G.weld := by
      simpa [WeldedInstance.edges, treeEdges, weldEdges] using he
    rcases hG.1.1 (u, w) hw with ⟨hu, hcu, hw', hcw⟩
    change col n u = n at hcu
    change col n w = n + 1 at hcw
    have hc := exit_col n
    rcases hi with hi | hi
    · change exitIdx n = u at hi
      rw [hi] at hc
      omega
    · change exitIdx n = w at hi
      rw [hi] at hc
      omega

lemma exit_colors_ne (n : ℕ) (hn : 2 ≤ n) (G : WeldedInstance n) (hG : G.IsValid) :
    G.color (.tree (2 ^ (n + 1))) ≠ G.color (.tree (2 ^ (n + 1) + 1)) := by
  apply hG.2
    (.tree (2 ^ (n + 1))) (by simpa using exit_child_edge n hn G 0 (by omega))
    (.tree (2 ^ (n + 1) + 1)) (exit_child_edge n hn G 1 (by omega))
  · simp
  · exact ⟨exitIdx n, by simpa using exit_child_incident n hn 0 (by omega),
      exit_child_incident n hn 1 (by omega)⟩

lemma exit_neighbor (n l : ℕ) (hn : 4 ≤ n) (hl : l ≤ n - 4)
    (G : WeldedInstance n) (hG : G.IsValid) (π : Equiv.Perm G.edges) (α : Fin 3) :
    G.Nb l π (exitIdx n) α =
      if α = G.color (.tree (2 ^ (n + 1))) then 2 ^ (n + 1)
      else if α = G.color (.tree (2 ^ (n + 1) + 1)) then 2 ^ (n + 1) + 1
      else exitIdx n := by
  classical
  have hn2 : 2 ≤ n := by omega
  have hv := exit_isVertex n hn2
  have hp0 := exit_child_parent n hn2 0 (by omega)
  have hp1 := exit_child_parent n hn2 1 (by omega)
  have hb0 := exit_child_bEdge n l hn2 hl G 0 (by omega) hn
  have hb1 := exit_child_bEdge n l hn2 hl G 1 (by omega) hn
  have he0 : Edge.tree (2 ^ (n + 1)) ∈ G.edges := by
    simpa using exit_child_edge n hn2 G 0 (by omega)
  have he1 := exit_child_edge n hn2 G 1 (by omega)
  have hi0 : (Edge.tree (2 ^ (n + 1))).Incident n (exitIdx n) := by
    simpa using exit_child_incident n hn2 0 (by omega)
  have hi1 := exit_child_incident n hn2 1 (by omega)
  have hne0 : exitIdx n ≠ 2 ^ (n + 1) := by
    have h := (root_size_bounds n hn2).1
    unfold exitIdx
    omega
  have hne1 : exitIdx n ≠ 2 ^ (n + 1) + 1 := by
    unfold exitIdx
    omega
  by_cases h0 : α = G.color (.tree (2 ^ (n + 1)))
  · subst α
    have ha := eAlpha_of_edge G hG.2 _ he0 _ hi0
    simp only [Nat.add_zero] at hp0 hb0
    simp [Nb, hv, ha, he0, hb0, Edge.tail, Edge.head, hp0, hne0]
  · by_cases h1 : α = G.color (.tree (2 ^ (n + 1) + 1))
    · subst α
      have ha := eAlpha_of_edge G hG.2 _ he1 _ hi1
      simp [Nb, hv, ha, he1, hb1, Edge.tail, Edge.head, hp1, hne1, h0]
    · have ha : G.eAlpha (exitIdx n) α = none := by
        unfold WeldedInstance.eAlpha
        split_ifs with h
        · obtain ⟨e, he, hc, hi⟩ := h
          rcases exit_incident_cases n hn2 G hG e he hi with rfl | rfl
          · exact False.elim (h0 hc.symm)
          · exact False.elim (h1 hc.symm)
        · rfl
      simp [Nb, hv, ha, h0, h1]

lemma exit_child_lt_label (n : ℕ) (hn : 2 ≤ n) :
    2 ^ (n + 1) + 1 < labelBound n + 1 := by
  have hp : 2 ^ (n + 2) ≤ 2 ^ (2 * n) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  rw [show n + 2 = (n + 1) + 1 by omega, pow_succ] at hp
  have hb := (root_size_bounds n hn).1
  unfold labelBound
  omega

lemma exit_Fnat_ne_iff (n l : ℕ) (hn : 4 ≤ n) (hl : l ≤ n - 4)
    (G : WeldedInstance n) (hG : G.IsValid)
    (σ : Equiv.Perm (Label n) × Equiv.Perm G.edges) (α : Fin 3) :
    Supplement.Fnat l G σ (σ.1 (exitLabelIdx n)).val α ≠ (σ.1 (exitLabelIdx n)).val ↔
      α = G.color (.tree (2 ^ (n + 1))) ∨
      α = G.color (.tree (2 ^ (n + 1) + 1)) := by
  classical
  have hb := exit_child_lt_label n (by omega)
  have hr : exitIdx n < labelBound n + 1 := (exitLabelIdx n).isLt
  have hN : G.Nb l σ.2 (exitIdx n) α < labelBound n + 1 := by
    rw [exit_neighbor n l hn hl G hG σ.2 α]
    split_ifs <;> omega
  have hne0 : 2 ^ (n + 1) ≠ exitIdx n := by
    have hp := (root_size_bounds n (by omega)).1
    unfold exitIdx
    omega
  have hne1 : 2 ^ (n + 1) + 1 ≠ exitIdx n := by unfold exitIdx; omega
  have heq : Supplement.Fnat l G σ (σ.1 (exitLabelIdx n)).val α ≠
      (σ.1 (exitLabelIdx n)).val ↔ G.Nb l σ.2 (exitIdx n) α ≠ exitIdx n := by
    unfold Supplement.Fnat
    rw [dif_pos (σ.1 (exitLabelIdx n)).isLt]
    change (G.F l σ (σ.1 (exitLabelIdx n)) α).val ≠ (σ.1 (exitLabelIdx n)).val ↔ _
    unfold WeldedInstance.F
    simp only [Equiv.symm_apply_apply]
    change (if h : G.Nb l σ.2 (exitIdx n) α < labelBound n + 1 then
      σ.1 ⟨G.Nb l σ.2 (exitIdx n) α, h⟩ else σ.1 (exitLabelIdx n)).val ≠
        (σ.1 (exitLabelIdx n)).val ↔ _
    rw [dif_pos hN]
    constructor
    · intro hnot hval
      apply hnot
      have hx : (⟨G.Nb l σ.2 (exitIdx n) α, hN⟩ : Label n) = exitLabelIdx n :=
        Fin.ext hval
      rw [hx]
    · intro hnot hval
      apply hnot
      have hx := σ.1.injective (Fin.ext hval)
      exact congrArg Fin.val hx
  rw [heq, exit_neighbor n l hn hl G hG σ.2 α]
  split_ifs with h0 h1 <;> simp_all

theorem exit_degree (n l : ℕ) (hn : 16 ≤ n) (hl : 2 ≤ l) (hln : l ≤ n - 4)
    (G : WeldedInstance n) (hG : G.IsValid)
    (σ : Equiv.Perm (Label n) × Equiv.Perm G.edges) :
    (Finset.univ.filter fun α : Fin 3 =>
      Supplement.Fnat l G σ (σ.1 (exitLabelIdx n)).val α ≠
        (σ.1 (exitLabelIdx n)).val).card = 2 := by
  classical
  have hset : (Finset.univ.filter fun α : Fin 3 =>
      Supplement.Fnat l G σ (σ.1 (exitLabelIdx n)).val α ≠
        (σ.1 (exitLabelIdx n)).val) =
      {G.color (.tree (2 ^ (n + 1))), G.color (.tree (2 ^ (n + 1) + 1))} := by
    ext α
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, exit_Fnat_ne_iff n l (by omega) hln G hG σ α]
  rw [hset]
  simp [exit_colors_ne n (by omega) G hG]

end WeldedPath.LoopProof

end

-- Solutions.WeldedPathKappaKernel
section

namespace WeldedPath.Supplement.KappaKernel

open WeldedInstance
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}

lemma kappa_nonneg (l : ℕ) (G : WeldedInstance n) (α : Fin 3) (u v : ℕ) :
    0 ≤ kappa l G α u v := by
  classical
  unfold kappa
  split <;> positivity

lemma sum_uniform_finset_le_one {X : Type*} [Fintype X] (f : X → ℕ)
    (hf : Function.Injective f) (S : Finset ℕ) (m : ℕ) (hSm : S.card ≤ m) :
    (∑ x, if f x ∈ S then 1 / (m : ℝ) else 0) ≤ 1 := by
  classical
  have hc : (Finset.univ.filter fun x => f x ∈ S).card ≤ m := by
    apply le_trans _ hSm
    exact Finset.card_le_card_of_injOn f
      (fun x hx => (Finset.mem_filter.mp hx).2)
      (fun _ _ _ _ h => hf h)
  by_cases hm : m = 0
  · simp [hm]
  · have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
    have hcr : ((Finset.univ.filter fun x => f x ∈ S).card : ℝ) ≤ m := by
      exact_mod_cast hc
    calc
      _ = ((Finset.univ.filter fun x => f x ∈ S).card : ℝ) * (1 / (m : ℝ)) := by
        rw [← Finset.sum_filter]
        simp
      _ ≤ (m : ℝ) * (1 / (m : ℝ)) :=
        mul_le_mul_of_nonneg_right hcr (by positivity)
      _ = 1 := by field_simp

lemma kappa_row_sum_le_one {X : Type*} [Fintype X] (f : X → ℕ)
    (hf : Function.Injective f) (l : ℕ) (G : WeldedInstance n) (α : Fin 3) (u : ℕ) :
    (∑ x, kappa l G α u (f x)) ≤ 1 := by
  classical
  cases hpd : permData l G u α with
  | none => simp [kappa, hpd]
  | some d =>
    obtain ⟨b, e, t⟩ := d
    cases t
    · simpa only [kappa, hpd, Bool.false_eq_true, false_and, true_and, false_or] using
        sum_uniform_finset_le_one f hf ((G.classEdges l b.1).image Edge.tail)
          (classSize l G b) (Finset.card_image_le)
    · simpa only [kappa, hpd, Bool.true_eq_false, false_and, true_and, or_false] using
        sum_uniform_finset_le_one f hf ((G.classEdges l b.1).image (Edge.head n))
          (classSize l G b) (Finset.card_image_le)

def classColor : EdgeClass → Fin 3
  | .tr _ α => α
  | .wld α => α

lemma bEdge_color {e : Edge} {b : EdgeClass} (he : G.bEdge l e = some b) :
    G.color e = classColor b := by
  cases e with
  | tree v =>
    simp only [WeldedInstance.bEdge] at he
    split at he
    · cases he
      rfl
    · simp at he
  | weld u v =>
    simp only [WeldedInstance.bEdge] at he
    cases he
    rfl

lemma class_color {b : PClass n l} {e e' : Edge}
    (he : e ∈ G.classEdges l b.1) (he' : e' ∈ G.classEdges l b.1) :
    G.color e = G.color e' :=
  (bEdge_color (Finset.mem_filter.mp he).2).trans
    (bEdge_color (Finset.mem_filter.mp he').2).symm

lemma eAlpha_spec {u : ℕ} {α : Fin 3} {e : Edge} (h : G.eAlpha u α = some e) :
    e ∈ G.edges ∧ G.color e = α ∧ e.Incident n u := by
  classical
  unfold WeldedInstance.eAlpha at h
  split at h
  · rename_i hh
    have hs := Classical.choose_spec hh
    cases h
    exact hs
  · simp at h

lemma permData_eAlpha {u : ℕ} {α : Fin 3} {b : PClass n l}
    {e : ↥(G.classEdges l b.1)} {t : Bool}
    (h : permData l G u α = some ⟨b, e, t⟩) : G.eAlpha u α = some e.1 := by
  classical
  unfold permData at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · cases h
        assumption
      · simp at h

lemma classData_ext {b b' : PClass n l} {e : ↥(G.classEdges l b.1)}
    {e' : ↥(G.classEdges l b'.1)} {t t' : Bool} (hb : b = b')
    (he : e.1 = e'.1) (ht : t = t') :
    (⟨b, e, t⟩ : (c : PClass n l) × ↥(G.classEdges l c.1) × Bool) = ⟨b', e', t'⟩ := by
  subst b'
  have he' : e = e' := Subtype.ext he
  subst e'
  subst t'
  rfl

lemma permData_of_class_edge (hG : G.IsValid) {b : PClass n l}
    (e : ↥(G.classEdges l b.1)) (u : ℕ) (hu : e.1.Incident n u) :
    permData l G u (G.color e.1) = some ⟨b, e, decide (u = e.1.tail)⟩ := by
  classical
  have he := Finset.mem_filter.mp e.2
  have hv : IsVertex n u := by
    rcases hu with rfl | rfl
    · exact (LoopProof.edge_endpoints hG he.1).1
    · exact (LoopProof.edge_endpoints hG he.1).2.1
  have ha := LoopProof.eAlpha_of_edge G hG.2 e.1 he.1 u hu
  unfold permData
  simp only [if_neg (not_not.mpr hv), ha]
  split
  · rename_i hh
    have hb : Classical.choose hh.2 = b.1 :=
      Option.some.inj ((Classical.choose_spec hh.2).2.1.symm.trans he.2)
    have hb' : (⟨Classical.choose hh.2, (Classical.choose_spec hh.2).1⟩ : PClass n l) = b :=
      Subtype.ext hb
    apply congrArg some
    exact classData_ext hb' rfl rfl
  · rename_i hh
    exact False.elim (hh ⟨he.1, b.1, b.2, he.2, hu⟩)

lemma class_tail_head_ne (hG : G.IsValid) {b : PClass n l}
    (e e' : ↥(G.classEdges l b.1)) : e.1.tail ≠ e'.1.head n := by
  have he := Finset.mem_filter.mp e.2
  have he' := Finset.mem_filter.mp e'.2
  have hc := LoopProof.same_class_cols hG he.1 he'.1
    (he.2.trans he'.2.symm) (by simp [he.2])
  have hd := (LoopProof.edge_endpoints hG he.1).2.2
  intro h
  have hv := congrArg (col n) h
  omega

lemma kappa_tail (hG : G.IsValid) {b : PClass n l}
    (e : ↥(G.classEdges l b.1)) (v : ℕ) :
    kappa l G (G.color e.1) e.1.tail v =
      if v ∈ (G.classEdges l b.1).image (Edge.head n) then
        1 / (classSize l G b : ℝ) else 0 := by
  classical
  have hp := permData_of_class_edge hG e e.1.tail (Or.inl rfl)
  simp only [kappa, hp, decide_true, true_and, Bool.true_eq_false, false_and, or_false]

lemma kappa_head (hG : G.IsValid) {b : PClass n l}
    (e : ↥(G.classEdges l b.1)) (v : ℕ) :
    kappa l G (G.color e.1) (e.1.head n) v =
      if v ∈ (G.classEdges l b.1).image Edge.tail then
        1 / (classSize l G b : ℝ) else 0 := by
  classical
  have hp := permData_of_class_edge hG e (e.1.head n) (Or.inr rfl)
  have hn : e.1.head n ≠ e.1.tail := (class_tail_head_ne hG e e).symm
  simp only [kappa, hp, decide_eq_false hn, Bool.false_eq_true, false_and,
    true_and, false_or]

lemma kappa_between_class (hG : G.IsValid) {b : PClass n l}
    (e e' : ↥(G.classEdges l b.1)) :
    kappa l G (G.color e.1) e.1.tail (e'.1.head n) =
      kappa l G (G.color e.1) (e'.1.head n) e.1.tail := by
  classical
  have hf : kappa l G (G.color e.1) e.1.tail (e'.1.head n) =
      1 / (classSize l G b : ℝ) := by
    rw [kappa_tail hG e]
    rw [if_pos (Finset.mem_image.mpr ⟨e'.1, e'.2, rfl⟩)]
  have hr : kappa l G (G.color e.1) (e'.1.head n) e.1.tail =
      1 / (classSize l G b : ℝ) := by
    rw [class_color e.2 e'.2, kappa_head hG e']
    rw [if_pos (Finset.mem_image.mpr ⟨e.1, e.2, rfl⟩)]
  exact hf.trans hr.symm

lemma kappa_symm_of_ne_zero (hG : G.IsValid) {α : Fin 3} {u v : ℕ}
    (hk : kappa l G α u v ≠ 0) : kappa l G α u v = kappa l G α v u := by
  classical
  cases hpd : permData l G u α with
  | none => simp [kappa, hpd] at hk
  | some d =>
    obtain ⟨b, e, t⟩ := d
    have hor := CrossingExclusion.permData_orientation hpd
    have hec := (eAlpha_spec (permData_eAlpha hpd)).2.1
    have hm : (t = true ∧ v ∈ (G.classEdges l b.1).image (Edge.head n)) ∨
        (t = false ∧ v ∈ (G.classEdges l b.1).image Edge.tail) := by
      by_contra hh
      exact hk (by simp only [kappa, hpd, if_neg hh])
    rw [← hec]
    rcases hm with ⟨ht, hv⟩ | ⟨ht, hv⟩
    · obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp hv
      rw [hor.1 ht]
      exact kappa_between_class hG e ⟨e', he'⟩
    · obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp hv
      rw [hor.2 ht, class_color e.2 he']
      exact (kappa_between_class hG ⟨e', he'⟩ e).symm

lemma kappa_symm (hG : G.IsValid) (α : Fin 3) (u v : ℕ) :
    kappa l G α u v = kappa l G α v u := by
  by_cases h : kappa l G α u v = 0
  · have hr : kappa l G α v u = 0 := by
      by_contra hn
      exact hn ((kappa_symm_of_ne_zero hG hn).trans h)
    exact h.trans hr.symm
  · exact kappa_symm_of_ne_zero hG h

lemma kappa_zero_of_not_vertex_left (l : ℕ) (G : WeldedInstance n)
    (α : Fin 3) {u : ℕ} (hu : ¬ IsVertex n u) (v : ℕ) :
    kappa l G α u v = 0 := by
  classical
  simp [kappa, permData, hu]

lemma kappa_zero_of_not_vertex_right (hG : G.IsValid) (α : Fin 3)
    (u : ℕ) {v : ℕ} (hv : ¬ IsVertex n v) : kappa l G α u v = 0 := by
  rw [kappa_symm hG α u v]
  exact kappa_zero_of_not_vertex_left l G α hv u

lemma kappa_le_inv_classSize {u : ℕ} {α : Fin 3} {b : PClass n l}
    {e : ↥(G.classEdges l b.1)} {t : Bool}
    (hpd : permData l G u α = some ⟨b, e, t⟩) (v : ℕ) :
    kappa l G α u v ≤ 1 / (classSize l G b : ℝ) := by
  classical
  simp only [kappa, hpd]
  split
  · exact le_rfl
  · positivity

lemma kappa_column_sum_le_one {X : Type*} [Fintype X] (f : X → ℕ)
    (hf : Function.Injective f) (hG : G.IsValid) (α : Fin 3) (v : ℕ) :
    (∑ x, kappa l G α (f x) v) ≤ 1 := by
  simp_rw [kappa_symm hG α _ v]
  exact kappa_row_sum_le_one f hf l G α v

lemma kappa_label_row_sum_le_one (l : ℕ) (G : WeldedInstance n) (α : Fin 3) (u : ℕ) :
    (∑ v : Label n, kappa l G α u v.1) ≤ 1 :=
  kappa_row_sum_le_one Fin.val Fin.val_injective l G α u

lemma kappa_label_column_sum_le_one (hG : G.IsValid) (α : Fin 3) (v : ℕ) :
    (∑ u : Label n, kappa l G α u.1 v) ≤ 1 :=
  kappa_column_sum_le_one Fin.val Fin.val_injective hG α v

lemma kappa_finset_row_sum_le_one (S : Finset ℕ) (l : ℕ) (G : WeldedInstance n)
    (α : Fin 3) (u : ℕ) : (∑ v ∈ S, kappa l G α u v) ≤ 1 := by
  simpa only [Finset.sum_coe_sort] using
    kappa_row_sum_le_one (fun v : S => v.1) Subtype.val_injective l G α u

lemma kappa_finset_column_sum_le_one (S : Finset ℕ) (hG : G.IsValid)
    (α : Fin 3) (v : ℕ) : (∑ u ∈ S, kappa l G α u v) ≤ 1 := by
  calc
    _ = ∑ u ∈ S, kappa l G α v u := by
      apply Finset.sum_congr rfl
      intro u _
      exact kappa_symm hG α u v
    _ ≤ 1 := kappa_finset_row_sum_le_one S l G α v

lemma finite_kernel_point_bound {X Y : Type*} [Fintype X]
    (K : X → Y → ℝ) (hK : ∀ x y, 0 ≤ K x y)
    (hcol : ∀ y, ∑ x, K x y ≤ 1) (p : X → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hp : ∀ x, p x ≤ M) (y : Y) :
    (∑ x, p x * K x y) ≤ M := by
  calc
    _ ≤ ∑ x, M * K x y := Finset.sum_le_sum fun x _ =>
      mul_le_mul_of_nonneg_right (hp x) (hK x y)
    _ = M * ∑ x, K x y := (Finset.mul_sum _ _ _).symm
    _ ≤ M * 1 := mul_le_mul_of_nonneg_left (hcol y) hM
    _ = M := mul_one M

lemma finite_kernel_abs_bound {X Y : Type*} [Fintype X]
    (K : X → Y → ℝ) (hK : ∀ x y, 0 ≤ K x y)
    (hcol : ∀ y, ∑ x, K x y ≤ 1) (p : X → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hp : ∀ x, |p x| ≤ M) (y : Y) :
    |∑ x, p x * K x y| ≤ M := by
  calc
    _ ≤ ∑ x, |p x * K x y| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x, |p x| * K x y := by
      apply Finset.sum_congr rfl
      intro x _
      rw [abs_mul, abs_of_nonneg (hK x y)]
    _ ≤ M := finite_kernel_point_bound K hK hcol (fun x => |p x|) M hM hp y

lemma finite_kernel_mass_le {X Y : Type*} [Fintype X] [Fintype Y]
    (K : X → Y → ℝ) (hrow : ∀ x, ∑ y, K x y ≤ 1)
    (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) :
    (∑ y, ∑ x, p x * K x y) ≤ ∑ x, p x := by
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro x _
  rw [← Finset.mul_sum]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (hrow x) (hp x)

lemma kappa_step_nonneg (l : ℕ) (G : WeldedInstance n) (α : Fin 3)
    (p : Label n → ℝ) (hp : ∀ x, 0 ≤ p x) (y : ℕ) :
    0 ≤ ∑ x : Label n, p x * kappa l G α x.1 y :=
  Finset.sum_nonneg fun x _ => mul_nonneg (hp x) (kappa_nonneg l G α x.1 y)

lemma kappa_step_mass_le (l : ℕ) (G : WeldedInstance n) (α : Fin 3)
    (p : Label n → ℝ) (hp : ∀ x, 0 ≤ p x) :
    (∑ y : Label n, ∑ x : Label n, p x * kappa l G α x.1 y.1) ≤ ∑ x, p x :=
  finite_kernel_mass_le (fun x y : Label n => kappa l G α x.1 y.1)
    (fun x => kappa_label_row_sum_le_one l G α x.1) p hp

lemma kappa_propagates_point_bound (hG : G.IsValid) (α : Fin 3)
    (p : Label n → ℝ) (M : ℝ) (hM : 0 ≤ M) (hp : ∀ x, p x ≤ M) (y : ℕ) :
    (∑ x : Label n, p x * kappa l G α x.1 y) ≤ M :=
  finite_kernel_point_bound (fun x : Label n => kappa l G α x.1)
    (fun x y => kappa_nonneg l G α x.1 y)
    (fun y => kappa_label_column_sum_le_one hG α y) p M hM hp y

lemma kappa_propagates_abs_bound (hG : G.IsValid) (α : Fin 3)
    (p : Label n → ℝ) (M : ℝ) (hM : 0 ≤ M) (hp : ∀ x, |p x| ≤ M) (y : ℕ) :
    |∑ x : Label n, p x * kappa l G α x.1 y| ≤ M :=
  finite_kernel_abs_bound (fun x : Label n => kappa l G α x.1)
    (fun x y => kappa_nonneg l G α x.1 y)
    (fun y => kappa_label_column_sum_le_one hG α y) p M hM hp y

end WeldedPath.Supplement.KappaKernel

end

-- Solutions.WeldedPathReferenceConditioning
section

namespace WeldedPath.Supplement.ForestFactorization

open scoped BigOperators
open FiniteWeightedForest
open Classical

variable {n : ℕ}

lemma component_edgeWeight_nonneg (l : ℕ) (G : WeldedInstance n) (H : AbsForest n)
    (E : Finset (Fin H.k × Fin H.k)) (φ : Fin H.k → Label n) :
    0 ≤ edgeWeight E (componentKernel l G H) φ := by
  apply Finset.prod_nonneg
  intro p _
  exact KappaKernel.kappa_nonneg l G (H.color p) (φ p.1).val (φ p.2).val

lemma componentScale_nonneg (l : ℕ) (G : WeldedInstance n) (H : AbsForest n)
    (s : Fin H.k) : 0 ≤ componentScale l G H s := by
  unfold componentScale
  apply mul_nonneg
  · apply one_div_nonneg.mpr
    apply mul_nonneg (one_div_nonneg.mpr (Nat.cast_nonneg _))
    apply Finset.sum_nonneg
    intro φ _
    exact component_edgeWeight_nonneg l G H _ φ
  · exact one_div_nonneg.mpr (Nat.cast_nonneg _)

lemma muComp_nonneg (l : ℕ) (G : WeldedInstance n) (H : AbsForest n)
    (hH : H.IsValid) (s : Fin H.k) (φ : Fin H.k → Label n) :
    0 ≤ H.muComp l G s φ := by
  rw [muComp_eq_componentCondition l G H hH s φ]
  apply mul_nonneg
  · split_ifs
    · exact one_div_nonneg.mpr (Nat.cast_nonneg _)
    · exact componentScale_nonneg l G H s
  · split_ifs
    · exact component_edgeWeight_nonneg l G H _ φ
    · exact le_rfl

lemma muRef_nonneg (l : ℕ) (G : WeldedInstance n) (H : AbsForest n)
    (hH : H.IsValid) (φ : Fin H.k → Label n) : 0 ≤ H.muRef l G φ := by
  exact Finset.prod_nonneg fun s _ => muComp_nonneg l G H hH s φ

lemma referenceScale_nonneg (l : ℕ) (G : WeldedInstance n) (H : AbsForest n) :
    0 ≤ referenceScale l G H := by
  apply Finset.prod_nonneg
  intro s _
  split_ifs
  · exact one_div_nonneg.mpr (Nat.cast_nonneg _)
  · exact componentScale_nonneg l G H s

lemma referenceScale_pos (l : ℕ) (G : WeldedInstance n) (H : AbsForest n)
    (hH : H.IsValid) (φ₀ : Fin H.k → Label n) (hμ : H.muRef l G φ₀ ≠ 0) :
    0 < referenceScale l G H :=
  lt_of_le_of_ne (referenceScale_nonneg l G H)
    (Ne.symm (referenceScale_ne_zero l G H hH φ₀ hμ))

/-- The unnormalized description law before removing collisions. -/
noncomputable def descriptionWeight (l : ℕ) (G : WeldedInstance n) (B : Finset ℕ)
    (D : Description n) (φ : Fin D.H.k → Label n) : ℝ :=
  if (∀ s ∈ D.sel, D.H.Wfix φ s = D.H.Wfix D.ϕ₀ s) ∧
      (∀ s ∈ D.sel, ∀ u, D.H.graph.Reachable s u →
        u ∉ D.H.Ctree φ s → (φ u).val ∉ B)
  then D.H.muRef l G φ else 0

/-- The description law is an explicit supported edge-product law. In
particular the fixed-data event itself introduces no dependence between
branches beyond their common fixed endpoint labels. -/
theorem descriptionWeight_eq_forestWeight (l : ℕ) (G : WeldedInstance n) (B : Finset ℕ)
    (D : Description n) (hD : D.IsValid) (φ : Fin D.H.k → Label n) :
    descriptionWeight l G B D φ = referenceScale l G D.H *
      forestWeight D.H.E (componentKernel l G D.H)
        (fun u x => referenceAllowed l D.H u x ∧ FixedData.coordinateCondition D B u x) φ := by
  unfold descriptionWeight
  simp only [FixedData.description_conditions_iff D hD B φ,
    muRef_eq_scale_forestWeight l G D.H hD.1 φ]
  unfold forestWeight
  simp only [forall_and, ite_and, mul_ite, mul_zero]
  split_ifs <;> rfl

/-- The only remaining restriction between the supported description law
and the good-assignment law is the injectivity (collision-free) mask. -/
theorem good_weight_eq_injective_mask (l : ℕ) (G : WeldedInstance n) (B : Finset ℕ)
    (D : Description n) (hD : D.IsValid) (φ : Fin D.H.k → Label n) :
    (if D.IsGood l G B φ then D.H.muRef l G φ else 0) =
      if Function.Injective φ then descriptionWeight l G B D φ else 0 := by
  have hnonneg := muRef_nonneg l G D.H hD.1 φ
  by_cases hμ : 0 < D.H.muRef l G φ
  · simp only [FixedData.isGood_iff_coordinateCondition l G D hD B φ,
      descriptionWeight, FixedData.description_conditions_iff D hD B φ, hμ, true_and]
    split_ifs <;> simp_all
  · have hzero : D.H.muRef l G φ = 0 := le_antisymm (le_of_not_gt hμ) hnonneg
    simp [hzero, descriptionWeight]

end WeldedPath.Supplement.ForestFactorization

end

-- Solutions.WeldedPathComponentCoefficients
section

namespace WeldedPath.Supplement.ComponentForest

open Classical ForestFactorization FixedDataFunctions
open scoped BigOperators

variable {n : ℕ}

theorem sqrt_muRef_product (l : ℕ) (G : WeldedInstance n) (H : AbsForest n)
    (hH : H.IsValid) (φ : Fin H.k → Label n) :
    Real.sqrt (H.muRef l G φ) = ∏ s : Roots H,
      Real.sqrt ((componentForest H s.val).muRef l G (restrict H s.val φ)) := by
  rw [muRef_eq_product_coordinates l G H hH]
  simp only [assignmentEquiv_restrict]
  exact Real.sqrt_prod Finset.univ (fun s _ =>
    muRef_nonneg l G _ (component_valid H hH s.val) _)

noncomputable def weightedLocalAmplitude (l : ℕ) (G : WeldedInstance n)
    (H : AbsForest n) (s : Roots H) (c : LocalAssignment H s → ℂ) :
    Hil (LocalAssignment H s) :=
  WithLp.toLp 2 (fun ψ => (Real.sqrt ((componentForest H s.val).muRef l G ψ) : ℂ) * c ψ)

/-- Multiplying the connected component amplitudes yields the literal
global square-root reference density, with no additional normalization. -/
theorem product_weighted_amplitudes (l : ℕ) (G : WeldedInstance n) (H : AbsForest n)
    (hH : H.IsValid) (c : (s : Roots H) → LocalAssignment H s → ℂ) :
    productAmplitude H (fun s => weightedLocalAmplitude l G H s (c s)) =
      WithLp.toLp 2 (fun φ => (Real.sqrt (H.muRef l G φ) : ℂ) *
        ∏ s : Roots H, c s (restrict H s.val φ)) := by
  ext φ
  change (∏ s : Roots H,
    (Real.sqrt ((componentForest H s.val).muRef l G (restrict H s.val φ)) : ℂ) *
      c s (restrict H s.val φ)) =
    (Real.sqrt (H.muRef l G φ) : ℂ) * ∏ s : Roots H, c s (restrict H s.val φ)
  rw [Finset.prod_mul_distrib, sqrt_muRef_product l G H hH φ, Complex.ofReal_prod]

/-- Original fixed-data coefficients may be used directly on each
connected restriction via the injective vertex-relabeling map. -/
theorem product_fixed_data_amplitudes (l : ℕ) (G : WeldedInstance n) (H : AbsForest n)
    (hH : H.IsValid) (sel : (s : Roots H) → Fin (H.comp s.val).card)
    (c : (s : Roots H) → Data H → ℂ) :
    productAmplitude H (fun s => weightedLocalAmplitude l G H s (fun ψ =>
      c s (dataLift H s.val ((componentForest H s.val).Wfix ψ (sel s))))) =
      WithLp.toLp 2 (fun φ => (Real.sqrt (H.muRef l G φ) : ℂ) *
        ∏ s : Roots H, c s (H.Wfix φ (vertexMap H s.val (sel s)))) := by
  rw [product_weighted_amplitudes l G H hH]
  apply congrArg (WithLp.toLp 2)
  funext φ
  congr 1
  apply Finset.prod_congr rfl
  intro s _
  rw [dataLift_wfix H hH s.val φ (sel s)]

end WeldedPath.Supplement.ComponentForest

end

-- Solutions.WeldedPathDescriptionAmplitude
section

namespace WeldedPath.Supplement.DescriptionCoefficients

open Classical ForestFactorization
open WeldedPath.WeightedCoefficients WeldedPath.HilbertSupport
open scoped BigOperators

variable {n : ℕ}

noncomputable def amplitude (l : ℕ) (G : WeldedInstance n) (H : AbsForest n)
    (B : Finset ℕ) (sel : Finset (Fin H.k)) (φ₀ : Fin H.k → Label n) :
    Hil (Fin H.k → Label n) :=
  WithLp.toLp 2 (fun φ => (Real.sqrt (descriptionWeight l G B ⟨H, sel, φ₀⟩ φ) : ℂ))

def descriptionGenerators (l : ℕ) (G : WeldedInstance n) (H : AbsForest n) (B : Finset ℕ) :
    Set (Hil (Fin H.k → Label n)) :=
  {f | ∃ sel φ₀, (Description.mk H sel φ₀).IsValid ∧ f = amplitude l G H B sel φ₀}

noncomputable def descriptionSpan (l : ℕ) (G : WeldedInstance n) (H : AbsForest n)
    (B : Finset ℕ) : Submodule ℂ (Hil (Fin H.k → Label n)) :=
  Submodule.span ℂ (descriptionGenerators l G H B)

theorem amplitude_injective_projection (l : ℕ) (G : WeldedInstance n) (H : AbsForest n)
    (B : Finset ℕ) (sel : Finset (Fin H.k)) (φ₀ : Fin H.k → Label n)
    (hD : (Description.mk H sel φ₀).IsValid) :
    (eventSpace Function.Injective).starProjection (amplitude l G H B sel φ₀) =
      WithLp.toLp 2 (fun φ => if (Description.mk H sel φ₀).IsGood l G B φ then
        (Real.sqrt (H.muRef l G φ) : ℂ) else 0) := by
  ext φ
  rw [eventSpace_projection, diagProj_apply]
  change (if Function.Injective φ then
    (Real.sqrt (descriptionWeight l G B ⟨H, sel, φ₀⟩ φ) : ℂ) else 0) = _
  have hh := good_weight_eq_injective_mask l G B (Description.mk H sel φ₀) hD φ
  have he := congrArg (fun x : ℝ => (Real.sqrt x : ℂ)) hh
  by_cases hg : (Description.mk H sel φ₀).IsGood l G B φ <;>
    by_cases hi : Function.Injective φ <;>
    simpa only [hg, hi, if_true, if_false, Real.sqrt_zero, Complex.ofReal_zero] using he.symm

end WeldedPath.Supplement.DescriptionCoefficients

end

-- Solutions.WeldedPathCollisionStability
section

namespace WeldedPath.CollisionStability

open scoped BigOperators
open Classical WeightedCoefficients CoefficientStability HilbertSupport

variable {Ω D ι χ : Type*} [Fintype Ω] [DecidableEq Ω]
  [Fintype ι] [Fintype χ] [DecidableEq D]

lemma eventSpace_mono (P Q : Ω → Prop) (hPQ : ∀ ω, P ω → Q ω) :
    eventSpace P ≤ eventSpace Q := by
  intro f hf ω hω
  exact hf ω (fun hP => hω (hPQ ω hP))

lemma event_projection_split (P F : Ω → Prop) (hFP : ∀ ω, F ω → P ω)
    (f : Hil Ω) :
    (eventSpace P).starProjection f =
      (eventSpace F).starProjection f +
        (eventSpace (fun ω => P ω ∧ ¬F ω)).starProjection f := by
  classical
  simp only [eventSpace_projection]
  ext ω
  by_cases hP : P ω <;> by_cases hF : F ω
  · simp [diagProj_apply, hP, hF]
  · simp [diagProj_apply, hP, hF]
  · exact (hP (hFP ω hF)).elim
  · simp [diagProj_apply, hP, hF]

/-- Local fixed-event parts are discarded by minimality. The remaining event
parts are controlled by the actual conditional bounds on each data fiber. -/
theorem pair_energy_bound
    (μ : Ω → ℝ) (hμ : ∀ ω, 0 ≤ μ ω) (data : ι → Ω → D)
    (S R : Submodule ℂ (Hil Ω)) (P : Ω → Prop) (F : ι → Ω → Prop)
    (hFP : ∀ i ω, F i ω → P ω)
    (hfixed : ∀ i v, v ∈ dataSpace μ (data i) →
      (eventSpace (F i)).starProjection v ∈ S ⊓ Rᗮ)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hcap : ∀ i d,
      (∑ ω, if data i ω = d ∧ (P ω ∧ ¬F i ω) then μ ω else 0) ≤
        ε * ∑ ω, if data i ω = d then μ ω else 0)
    (f : Hil Ω) (hf : f ∈ (S ⊓ Rᗮ)ᗮ)
    (v : ι → Hil Ω) (hv : ∀ i, v i ∈ dataSpace μ (data i))
    (hdec : f = ∑ i, v i) (henergy : (∑ i, ‖v i‖ ^ 2) ≤ ‖f‖ ^ 2) :
    ‖(eventSpace P).starProjection f‖ ^ 2 ≤
      (Fintype.card ι : ℝ) * ε * ‖f‖ ^ 2 := by
  classical
  let k : ι → Hil Ω := fun i => (eventSpace (F i)).starProjection (v i)
  let r : ι → Hil Ω := fun i =>
    (eventSpace (fun ω => P ω ∧ ¬F i ω)).starProjection (v i)
  apply collision_from_decomposition (S ⊓ Rᗮ) (eventSpace P) f hf v k r ε hε
  · rw [hdec, map_sum]
    calc
      _ = ∑ i, (k i + r i) := by
        apply Finset.sum_congr rfl
        intro i _
        exact event_projection_split P (F i) (hFP i) (v i)
      _ = _ := Finset.sum_add_distrib
  · exact fun i => hfixed i (v i) (hv i)
  · intro i
    exact eventSpace_mono (F i) P (hFP i)
      ((eventSpace (F i)).starProjection_apply_mem (v i))
  · intro i
    obtain ⟨a, ha⟩ := (mem_dataSpace μ (data i) (v i)).mp (hv i)
    change ‖(eventSpace (fun ω => P ω ∧ ¬F i ω)).starProjection (v i)‖ ^ 2 ≤ _
    rw [← ha]
    exact conditional_event_bound μ hμ (data i) (fun ω => P ω ∧ ¬F i ω)
      ε (hcap i) a
  · exact henergy

/-- A finite union of pair events gives the collision estimate for a minimal
representative, with the number of pairs and local components explicit. -/
theorem collision_energy_bound
    (μ : Ω → ℝ) (hμ : ∀ ω, 0 ≤ μ ω) (data : ι → Ω → D)
    (S : Submodule ℂ (Hil Ω)) (Good : Ω → Prop)
    (P : χ → Ω → Prop) (F : χ → ι → Ω → Prop)
    (hbad : ∀ ω, ¬Good ω ↔ ∃ c, P c ω)
    (hFP : ∀ c i ω, F c i ω → P c ω)
    (hfixed : ∀ c i v, v ∈ dataSpace μ (data i) →
      (eventSpace (F c i)).starProjection v ∈ S ⊓ (eventSpace Good)ᗮ)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hcap : ∀ c i d,
      (∑ ω, if data i ω = d ∧ (P c ω ∧ ¬F c i ω) then μ ω else 0) ≤
        ε * ∑ ω, if data i ω = d then μ ω else 0)
    (f : Hil Ω) (hf : f ∈ (S ⊓ (eventSpace Good)ᗮ)ᗮ)
    (v : ι → Hil Ω) (hv : ∀ i, v i ∈ dataSpace μ (data i))
    (hdec : f = ∑ i, v i) (henergy : (∑ i, ‖v i‖ ^ 2) ≤ ‖f‖ ^ 2) :
    ‖(eventSpace Good)ᗮ.starProjection f‖ ^ 2 ≤
      (Fintype.card χ : ℝ) * (Fintype.card ι : ℝ) * ε * ‖f‖ ^ 2 := by
  classical
  have he : (eventSpace Good)ᗮ = eventSpace (fun ω => ∃ c, P c ω) := by
    rw [eventSpace_orthogonal]
    congr 1
    funext ω
    exact propext (hbad ω)
  have hp : (eventSpace Good)ᗮ.starProjection f =
      (eventSpace (fun ω => ∃ c, P c ω)).starProjection f :=
    congrArg (fun T : Submodule ℂ (Hil Ω) => T.starProjection f) he
  rw [hp]
  calc
    _ ≤ ∑ c, ‖(eventSpace (P c)).starProjection f‖ ^ 2 := event_union_norm_sq P f
    _ ≤ ∑ _c : χ, (Fintype.card ι : ℝ) * ε * ‖f‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro c _
      exact pair_energy_bound μ hμ data S (eventSpace Good) (P c) (F c)
        (hFP c) (hfixed c) ε hε (hcap c) f hf v hv hdec henergy
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-- Conditional fiber bounds and a controlled local decomposition supply a
unique stable coefficient representative after the bad-event kernel is removed. -/
theorem stable_representative_of_fiber_bounds
    (μ : Ω → ℝ) (hμ : ∀ ω, 0 ≤ μ ω) (data : ι → Ω → D)
    (S : Submodule ℂ (Hil Ω)) (Good : Ω → Prop)
    (P : χ → Ω → Prop) (F : χ → ι → Ω → Prop)
    (hbad : ∀ ω, ¬Good ω ↔ ∃ c, P c ω)
    (hFP : ∀ c i ω, F c i ω → P c ω)
    (hfixed : ∀ c i v, v ∈ dataSpace μ (data i) →
      (eventSpace (F c i)).starProjection v ∈ S ⊓ (eventSpace Good)ᗮ)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hcap : ∀ c i d,
      (∑ ω, if data i ω = d ∧ (P c ω ∧ ¬F c i ω) then μ ω else 0) ≤
        ε * ∑ ω, if data i ω = d then μ ω else 0)
    (hdecomp : ∀ f ∈ S, f ∈ (S ⊓ (eventSpace Good)ᗮ)ᗮ →
      ∃ v : ι → Hil Ω, (∀ i, v i ∈ dataSpace μ (data i)) ∧
        f = ∑ i, v i ∧ (∑ i, ‖v i‖ ^ 2) ≤ ‖f‖ ^ 2)
    (hsmall : (Fintype.card χ : ℝ) * (Fintype.card ι : ℝ) * ε ≤ 1 / 2)
    (f₀ : Hil Ω) (hf₀ : f₀ ∈ S) :
    ∃! f : Hil Ω, f ∈ S ∧ f ∈ (S ⊓ (eventSpace Good)ᗮ)ᗮ ∧
      (eventSpace Good).starProjection f = (eventSpace Good).starProjection f₀ ∧
      ‖f‖ ^ 2 ≤ 2 * ‖(eventSpace Good).starProjection f₀‖ ^ 2 := by
  apply stable_representative S (eventSpace Good) ?_ f₀ hf₀
  intro f hfS hf
  obtain ⟨v, hv, hdec, henergy⟩ := hdecomp f hfS hf
  exact (collision_energy_bound μ hμ data S Good P F hbad hFP hfixed ε hε hcap
    f hf v hv hdec henergy).trans (mul_le_mul_of_nonneg_right hsmall (sq_nonneg ‖f‖))

end WeldedPath.CollisionStability

end

-- Solutions.WeldedPathFixedAvoidance
section

namespace WeldedPath.Supplement.FixedAvoidance

variable {n : ℕ}

lemma sfix_not_ctree_weld (H : AbsForest n) (φ : Fin H.k → Label n) (s : Fin H.k)
    {v : Fin H.k} (hv : v ∈ H.Sfix φ s) (hc : v ∉ H.Ctree φ s) :
    (φ v).1 ∈ Vweld n := by
  classical
  obtain ⟨e, _, hw, hor⟩ := (Finset.mem_filter.mp
    ((Finset.mem_union.mp hv).resolve_left hc)).2
  rcases hor with ⟨_, hev⟩ | ⟨_, hev⟩
  · exact hev ▸ hw.2
  · exact hev ▸ hw.1

lemma avoid_ctree_iff_avoid_sfix_of_agree (H : AbsForest n)
    (φ φ₀ : Fin H.k → Label n) (s : Fin H.k) (B : Finset ℕ)
    (hB : Disjoint B (Vweld n)) (hφ : ∀ u ∈ H.Sfix φ₀ s, φ u = φ₀ u) :
    (∀ u, u ∉ H.Ctree φ₀ s → (φ u).1 ∉ B) ↔
      (∀ u, u ∉ H.Sfix φ₀ s → (φ u).1 ∉ B) := by
  classical
  constructor
  · intro h u hu
    exact h u (fun hc => hu (FixedData.ctree_subset_sfix H φ₀ s hc))
  · intro h u hu
    by_cases hs : u ∈ H.Sfix φ₀ s
    · have hw := sfix_not_ctree_weld H φ₀ s hs hu
      rw [hφ u hs]
      exact fun hb => Finset.disjoint_left.mp hB hb hw
    · exact h u hs

lemma avoid_tree_iff_avoid_free_of_wfix (H : AbsForest n) (hH : H.IsValid)
    (φ φ₀ : Fin H.k → Label n) (s : Fin H.k) (B : Finset ℕ)
    (hB : Disjoint B (Vweld n)) (hw : H.Wfix φ s = H.Wfix φ₀ s) :
    (∀ u, u ∉ H.Ctree φ s → (φ u).1 ∉ B) ↔
      (∀ u, u ∉ H.Sfix φ₀ s → (φ u).1 ∉ B) := by
  have hφ := (FixedData.wfix_eq_iff_agree_sfix H hH φ φ₀ s).mp hw
  have hc : H.Ctree φ s = H.Ctree φ₀ s := congrArg Prod.fst hw
  rw [hc]
  exact avoid_ctree_iff_avoid_sfix_of_agree H φ φ₀ s B hB hφ

lemma connected_fixed_avoidance_iff (H : AbsForest n) (hH : H.IsValid)
    (φ φ₀ : Fin H.k → Label n) (s : Fin H.k)
    (hs : ∀ u, H.graph.Reachable s u) (B : Finset ℕ) (hB : Disjoint B (Vweld n)) :
    (H.Wfix φ s = H.Wfix φ₀ s ∧
      ∀ u, H.graph.Reachable s u → u ∉ H.Ctree φ s → (φ u).1 ∉ B) ↔
    ((∀ u ∈ H.Sfix φ₀ s, φ u = φ₀ u) ∧
      ∀ u, u ∉ H.Sfix φ₀ s → (φ u).1 ∉ B) := by
  constructor
  · rintro ⟨hw, hb⟩
    refine ⟨(FixedData.wfix_eq_iff_agree_sfix H hH φ φ₀ s).mp hw, ?_⟩
    exact (avoid_tree_iff_avoid_free_of_wfix H hH φ φ₀ s B hB hw).mp
      (fun u => hb u (hs u))
  · rintro ⟨hφ, hb⟩
    have hw := (FixedData.wfix_eq_iff_agree_sfix H hH φ φ₀ s).mpr hφ
    refine ⟨hw, ?_⟩
    intro u _ hu
    exact (avoid_tree_iff_avoid_free_of_wfix H hH φ φ₀ s B hB hw).mpr hb u hu

end WeldedPath.Supplement.FixedAvoidance

end

-- Solutions.WeldedPathWeldClasses
section

namespace WeldedPath.WeldClasses

open Classical LoopProof

theorem mem_weld_class {n l : ℕ} {G : WeldedInstance n} (α : Fin 3) (e : Edge) :
    e ∈ G.classEdges l (.wld α) ↔ e ∈ G.weldEdges ∧ G.color e = α := by
  cases e with
  | tree v =>
    by_cases h : n - l ≤ col n v ∧ col n v ≤ n + l <;>
      simp [WeldedInstance.classEdges, WeldedInstance.bEdge, WeldedInstance.weldEdges, h]
  | weld u w =>
    simp [WeldedInstance.classEdges, WeldedInstance.bEdge, WeldedInstance.edges,
      WeldedInstance.treeEdges, WeldedInstance.weldEdges]

theorem weld_classes_disjoint {n l : ℕ} (G : WeldedInstance n) {α β : Fin 3}
    (h : α ≠ β) : Disjoint (G.classEdges l (.wld α)) (G.classEdges l (.wld β)) := by
  apply Finset.disjoint_left.mpr
  intro e he he'
  exact h (((mem_weld_class α e).mp he).2.symm.trans ((mem_weld_class β e).mp he').2)

theorem tail_injective {n l : ℕ} {G : WeldedInstance n} (hG : G.IsProperColoring)
    (α : Fin 3) : Set.InjOn Edge.tail (G.classEdges l (.wld α)) := by
  intro e he e' he' htail
  by_contra hne
  have hc := hG e (Finset.mem_filter.mp he).1 e' (Finset.mem_filter.mp he').1 hne
    ⟨e.tail, Or.inl rfl, Or.inl htail⟩
  exact hc (((mem_weld_class α e).mp he).2.trans ((mem_weld_class α e').mp he').2.symm)

theorem head_injective {n l : ℕ} {G : WeldedInstance n} (hG : G.IsProperColoring)
    (α : Fin 3) : Set.InjOn (Edge.head n) (G.classEdges l (.wld α)) := by
  intro e he e' he' hhead
  by_contra hne
  have hc := hG e (Finset.mem_filter.mp he).1 e' (Finset.mem_filter.mp he').1 hne
    ⟨e.head n, Or.inr rfl, Or.inr hhead⟩
  exact hc (((mem_weld_class α e).mp he).2.trans ((mem_weld_class α e').mp he').2.symm)

theorem left_leaf_bounds {n v : ℕ} (hv : IsVertex n v) (hc : col n v = n) :
    2 ^ n - 1 ≤ v ∧ v < 2 ^ (n + 1) - 1 := by
  have hleft : v < 2 ^ (n + 1) - 1 := by
    by_contra h
    have hh := col_right_ge n v hv (by omega)
    omega
  have hlog : Nat.log 2 (v + 1) = n := by simpa [col, hleft] using hc
  have hh := Nat.pow_log_le_self 2 (by omega : v + 1 ≠ 0)
  rw [hlog] at hh
  exact ⟨by omega, hleft⟩

theorem left_leaf_of_bounds {n v : ℕ} (hn : 1 ≤ n)
    (hlo : 2 ^ n - 1 ≤ v) (hhi : v < 2 ^ (n + 1) - 1) :
    IsVertex n v ∧ col n v = n ∧ parent n v = some ((v - 1) / 2) := by
  have hpow := Nat.two_pow_pos n
  have hroot := pow_root_ge_two n
  have hv : IsVertex n v := by
    rw [IsVertex, numV_eq]
    omega
  have hc : col n v = n := by
    rw [col, if_pos hhi]
    exact Nat.log_eq_of_pow_le_of_lt_pow (by omega) (by omega)
  refine ⟨hv, hc, ?_⟩
  simp [parent, hv, hc, hn]

theorem weld_class_tail_bounds {n l : ℕ} {G : WeldedInstance n} (hG : G.IsWeld)
    {α : Fin 3} {e : Edge} (he : e ∈ G.classEdges l (.wld α)) :
    2 ^ n - 1 ≤ e.tail ∧ e.tail < 2 ^ (n + 1) - 1 := by
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ((mem_weld_class α e).mp he).1
  have hh := hG.1 p hp
  exact left_leaf_bounds hh.1 hh.2.1

theorem weld_class_card_le {n l : ℕ} {G : WeldedInstance n} (hG : G.IsValid)
    (α : Fin 3) : (G.classEdges l (.wld α)).card ≤ 2 ^ n := by
  have hh := Finset.card_le_card_of_injOn Edge.tail
    (s := G.classEdges l (.wld α)) (t := Finset.Ico (2 ^ n - 1) (2 ^ (n + 1) - 1))
    (fun e he => Finset.mem_Ico.mpr (weld_class_tail_bounds hG.1 he))
    (tail_injective hG.2 α)
  have hp := Nat.two_pow_pos n
  have hcard : (Finset.Ico (2 ^ n - 1) (2 ^ (n + 1) - 1)).card = 2 ^ n := by
    rw [Nat.card_Ico, pow_succ]
    omega
  simpa only [hcard] using hh

private theorem three_colors_cover (a b c d : Fin 3) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) : d = a ∨ d = b ∨ d = c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> simp_all

theorem weld_color_at_leaf {n l v : ℕ} {G : WeldedInstance n} (hG : G.IsValid)
    (hn : 1 ≤ n) (hv : IsVertex n v) (hc : col n v = n) (α : Fin 3)
    (htc : G.color (.tree v) ≠ α) :
    ∃ e ∈ G.classEdges l (.wld α), e.tail = v := by
  have hbounds := left_leaf_bounds hv hc
  have hpv := (left_leaf_of_bounds hn hbounds.1 hbounds.2).2.2
  have ht : Edge.tree v ∈ G.edges := tree_mem_iff.mpr ⟨hv, by simp [hpv]⟩
  obtain ⟨p, q, hpq, hs⟩ := Finset.card_eq_two.mp (hG.1.2.1 v ⟨hv, Or.inl hc⟩)
  have hp : p ∈ G.weld ∧ (p.1 = v ∨ p.2 = v) := by
    apply Finset.mem_filter.mp
    rw [hs]
    simp
  have hq : q ∈ G.weld ∧ (q.1 = v ∨ q.2 = v) := by
    apply Finset.mem_filter.mp
    rw [hs]
    simp
  have hpt : p.1 = v := by
    rcases hp.2 with h | h
    · exact h
    · have hh := (hG.1.1 p hp.1).2.2.2
      rw [h, hc] at hh
      omega
  have hqt : q.1 = v := by
    rcases hq.2 with h | h
    · exact h
    · have hh := (hG.1.1 q hq.1).2.2.2
      rw [h, hc] at hh
      omega
  have hep : Edge.weld p.1 p.2 ∈ G.edges := weld_mem_iff.mpr hp.1
  have heq : Edge.weld q.1 q.2 ∈ G.edges := weld_mem_iff.mpr hq.1
  have htp := hG.2 (.tree v) ht (.weld p.1 p.2) hep (by simp)
    ⟨v, Or.inl rfl, Or.inl hpt.symm⟩
  have htq := hG.2 (.tree v) ht (.weld q.1 q.2) heq (by simp)
    ⟨v, Or.inl rfl, Or.inl hqt.symm⟩
  have hpq' : Edge.weld p.1 p.2 ≠ Edge.weld q.1 q.2 := by
    intro h
    exact hpq (Prod.ext (congrArg Edge.tail h) (congrArg (Edge.head n) h))
  have hpqc := hG.2 (.weld p.1 p.2) hep (.weld q.1 q.2) heq hpq'
    ⟨v, Or.inl hpt.symm, Or.inl hqt.symm⟩
  rcases three_colors_cover (G.color (.tree v)) (G.color (.weld p.1 p.2))
      (G.color (.weld q.1 q.2)) α htp htq hpqc with h | h | h
  · exact (htc h.symm).elim
  · refine ⟨.weld p.1 p.2, (mem_weld_class α _).mpr ⟨?_, h.symm⟩, hpt⟩
    exact Finset.mem_image.mpr ⟨p, hp.1, rfl⟩
  · refine ⟨.weld q.1 q.2, (mem_weld_class α _).mpr ⟨?_, h.symm⟩, hqt⟩
    exact Finset.mem_image.mpr ⟨q, hq.1, rfl⟩

theorem weld_class_card_ge {n l : ℕ} {G : WeldedInstance n} (hG : G.IsValid)
    (hn : 1 ≤ n) (α : Fin 3) : 2 ^ (n - 1) ≤ (G.classEdges l (.wld α)).card := by
  have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := by
    calc
      2 ^ n = 2 ^ ((n - 1) + 1) := congrArg (2 ^ ·) (by omega)
      _ = 2 * 2 ^ (n - 1) := by rw [pow_succ, Nat.mul_comm]
  have hpow' : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ, Nat.mul_comm]
  have hpos := Nat.two_pow_pos (n - 1)
  have hpairs (j : Fin (2 ^ (n - 1))) :
      ∃ e ∈ G.classEdges l (.wld α),
        e.tail = 2 ^ n - 1 + 2 * j.val ∨ e.tail = 2 ^ n - 1 + 2 * j.val + 1 := by
    let u := 2 ^ n - 1 + 2 * j.val
    have hj := j.isLt
    have hu := left_leaf_of_bounds (v := u) hn (by dsimp [u]; omega)
      (by dsimp [u]; omega)
    have hu' := left_leaf_of_bounds (v := u + 1) hn (by dsimp [u]; omega)
      (by dsimp [u]; omega)
    have ht : Edge.tree u ∈ G.edges := tree_mem_iff.mpr ⟨hu.1, by simp [hu.2.2]⟩
    have ht' : Edge.tree (u + 1) ∈ G.edges := tree_mem_iff.mpr ⟨hu'.1, by simp [hu'.2.2]⟩
    have hparent : (u - 1) / 2 = u / 2 := by dsimp [u]; omega
    have hcolors : G.color (.tree u) ≠ G.color (.tree (u + 1)) := by
      apply hG.2 (.tree u) ht (.tree (u + 1)) ht' (by simp)
      refine ⟨(u - 1) / 2, Or.inr ?_, Or.inr ?_⟩
      · simp [Edge.head, hu.2.2]
      · simp [Edge.head, hu'.2.2, hparent]
    by_cases hcu : G.color (.tree u) ≠ α
    · obtain ⟨e, he, htail⟩ := weld_color_at_leaf hG hn hu.1 hu.2.1 α hcu
      exact ⟨e, he, Or.inl htail⟩
    · have hcu' : G.color (.tree (u + 1)) ≠ α := by
        intro h
        exact hcolors ((not_ne_iff.mp hcu).trans h.symm)
      obtain ⟨e, he, htail⟩ := weld_color_at_leaf hG hn hu'.1 hu'.2.1 α hcu'
      exact ⟨e, he, Or.inr htail⟩
  choose f hf using hpairs
  let F : Fin (2 ^ (n - 1)) → G.classEdges l (.wld α) := fun j => ⟨f j, (hf j).1⟩
  have hinj : Function.Injective F := by
    intro j k h
    have heq : f j = f k := congrArg Subtype.val h
    have ht := congrArg Edge.tail heq
    rcases (hf j).2 with hj | hj <;> rcases (hf k).2 with hk | hk <;>
      apply Fin.ext <;> omega
  simpa only [Fintype.card_fin, Fintype.card_coe] using Fintype.card_le_of_injective F hinj

theorem weld_class_card_bounds {n l : ℕ} {G : WeldedInstance n} (hG : G.IsValid)
    (hn : 1 ≤ n) (α : Fin 3) :
    2 ^ (n - 1) ≤ (G.classEdges l (.wld α)).card ∧
      (G.classEdges l (.wld α)).card ≤ 2 ^ n :=
  ⟨weld_class_card_ge hG hn α, weld_class_card_le hG α⟩

end WeldedPath.WeldClasses

end

-- Solutions.WeldedPathNearWeldClasses
section

namespace WeldedPath.NearWeldClasses

open Classical LoopProof

/-- Heap coordinates in either of the two binary trees. -/
def heapNode (n : ℕ) (right : Bool) (u : ℕ) : ℕ :=
  (if right then 2 ^ (n + 1) - 1 else 0) + u

def heapCol (n : ℕ) (right : Bool) (d : ℕ) : ℕ :=
  if right then 2 * n + 1 - d else d

theorem heap_node_spec {n d u : ℕ} (right : Bool)
    (hd : 1 ≤ d) (hdn : d ≤ n)
    (hlo : 2 ^ d - 1 ≤ u) (hhi : u < 2 ^ (d + 1) - 1) :
    IsVertex n (heapNode n right u) ∧
      col n (heapNode n right u) = heapCol n right d ∧
      parent n (heapNode n right u) = some (heapNode n right ((u - 1) / 2)) := by
  have hroot := pow_root_ge_two n
  have hpow := Nat.two_pow_pos d
  have hdpow : 2 ≤ 2 ^ d := by
    calc
      2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ d := Nat.pow_le_pow_right (by decide) hd
  have hupper : u < 2 ^ (n + 1) - 1 := by
    have hh := Nat.pow_le_pow_right (n := 2) (by decide : 1 ≤ 2)
      (show d + 1 ≤ n + 1 by omega)
    omega
  have hlog : Nat.log 2 (u + 1) = d :=
    Nat.log_eq_of_pow_le_of_lt_pow (by omega) (by omega)
  have hup : 1 ≤ u := by omega
  cases right with
  | false =>
    simp only [heapNode, Bool.false_eq_true, if_false, zero_add, heapCol]
    have hv : IsVertex n u := by rw [IsVertex, numV_eq]; omega
    have hc : col n u = d := by simp [col, hupper, hlog]
    refine ⟨hv, hc, ?_⟩
    simp [parent, hv, hc, hd, hdn]
  | true =>
    simp only [heapNode, if_true, heapCol]
    let R := 2 ^ (n + 1) - 1
    have hv : IsVertex n (R + u) := by
      rw [IsVertex, numV_eq]
      dsimp [R]
      omega
    have hc : col n (R + u) = 2 * n + 1 - d := by
      rw [col, if_neg (by dsimp [R]; omega)]
      change 2 * n + 1 - Nat.log 2 (R + u - R + 1) = _
      rw [Nat.add_sub_cancel_left, hlog]
    refine ⟨hv, hc, ?_⟩
    have hfirst : ¬ (IsVertex n (R + u) ∧ 1 ≤ col n (R + u) ∧
        col n (R + u) ≤ n) := by rw [hc]; omega
    have hsecond : IsVertex n (R + u) ∧ n + 1 ≤ col n (R + u) ∧
        col n (R + u) ≤ 2 * n := by rw [hc]; exact ⟨hv, by omega, by omega⟩
    change parent n (R + u) = some (R + (u - 1) / 2)
    rw [parent, if_neg hfirst, if_pos hsecond]
    congr 1
    dsimp [R]
    omega

private theorem three_colors_cover (a b c d : Fin 3) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) : d = a ∨ d = b ∨ d = c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> simp_all

theorem child_color_of_parent_ne {n : ℕ} {G : WeldedInstance n}
    (hG : G.IsProperColoring) (p a b : ℕ)
    (hp : Edge.tree p ∈ G.edges) (ha : Edge.tree a ∈ G.edges)
    (hb : Edge.tree b ∈ G.edges) (hpa : p ≠ a) (hpb : p ≠ b) (hab : a ≠ b)
    (hapar : parent n a = some p) (hbpar : parent n b = some p)
    (α : Fin 3) (hc : G.color (.tree p) ≠ α) :
    G.color (.tree a) = α ∨ G.color (.tree b) = α := by
  have hca := hG (.tree p) hp (.tree a) ha (by simpa using hpa)
    ⟨p, Or.inl rfl, Or.inr (by simp [Edge.head, hapar])⟩
  have hcb := hG (.tree p) hp (.tree b) hb (by simpa using hpb)
    ⟨p, Or.inl rfl, Or.inr (by simp [Edge.head, hbpar])⟩
  have hcab := hG (.tree a) ha (.tree b) hb (by simpa using hab)
    ⟨p, Or.inr (by simp [Edge.head, hapar]), Or.inr (by simp [Edge.head, hbpar])⟩
  rcases three_colors_cover _ _ _ α hca hcb hcab with h | h | h
  · exact (hc h.symm).elim
  · exact Or.inl h.symm
  · exact Or.inr h.symm

theorem pow_two_levels {n : ℕ} (hn : 2 ≤ n) :
    2 ^ n = 4 * 2 ^ (n - 2) ∧ 2 ^ (n - 1) = 2 * 2 ^ (n - 2) := by
  constructor
  · rw [show n = (n - 2) + 2 by omega, pow_add]
    norm_num
    omega
  · rw [show n - 1 = (n - 2) + 1 by omega, pow_succ]
    omega

theorem quad_leaf_spec {n : ℕ} (hn : 2 ≤ n) (right : Bool)
    (j : Fin (2 ^ (n - 2))) (k : Fin 4) :
    IsVertex n (heapNode n right (2 ^ n - 1 + 4 * j.val + k.val)) ∧
      col n (heapNode n right (2 ^ n - 1 + 4 * j.val + k.val)) = heapCol n right n ∧
      parent n (heapNode n right (2 ^ n - 1 + 4 * j.val + k.val)) =
        some (heapNode n right (2 ^ (n - 1) - 1 + 2 * j.val + k.val / 2)) := by
  have hp := pow_two_levels hn
  have hpos := Nat.two_pow_pos (n - 2)
  have hsucc : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ, Nat.mul_comm]
  have hj := j.isLt
  have hk := k.isLt
  have hs := heap_node_spec (n := n) (d := n)
    (u := 2 ^ n - 1 + 4 * j.val + k.val) right (by omega) le_rfl (by omega) (by omega)
  have hdiv : (2 ^ n - 1 + 4 * j.val + k.val - 1) / 2 =
      2 ^ (n - 1) - 1 + 2 * j.val + k.val / 2 := by omega
  simpa only [hdiv] using hs

theorem quad_parent_spec {n : ℕ} (hn : 2 ≤ n) (right : Bool)
    (j : Fin (2 ^ (n - 2))) (k : Fin 2) :
    IsVertex n (heapNode n right (2 ^ (n - 1) - 1 + 2 * j.val + k.val)) ∧
      col n (heapNode n right (2 ^ (n - 1) - 1 + 2 * j.val + k.val)) =
        heapCol n right (n - 1) ∧
      parent n (heapNode n right (2 ^ (n - 1) - 1 + 2 * j.val + k.val)) =
        some (heapNode n right (2 ^ (n - 2) - 1 + j.val)) := by
  have hp := pow_two_levels hn
  have hpos := Nat.two_pow_pos (n - 2)
  have hsucc : 2 ^ ((n - 1) + 1) = 2 ^ n := congrArg (2 ^ ·) (by omega)
  have hj := j.isLt
  have hk := k.isLt
  have hs := heap_node_spec (n := n) (d := n - 1)
    (u := 2 ^ (n - 1) - 1 + 2 * j.val + k.val) right
    (by omega) (by omega) (by omega) (by omega)
  have hdiv : (2 ^ (n - 1) - 1 + 2 * j.val + k.val - 1) / 2 =
      2 ^ (n - 2) - 1 + j.val := by omega
  simpa only [hdiv] using hs

theorem leaf_quad_has_color {n : ℕ} {G : WeldedInstance n}
    (hG : G.IsProperColoring) (hn : 2 ≤ n) (right : Bool)
    (j : Fin (2 ^ (n - 2))) (α : Fin 3) :
    ∃ k : Fin 4,
      G.color (.tree (heapNode n right (2 ^ n - 1 + 4 * j.val + k.val))) = α := by
  let v (k : Fin 4) := heapNode n right (2 ^ n - 1 + 4 * j.val + k.val)
  let p (k : Fin 2) := heapNode n right (2 ^ (n - 1) - 1 + 2 * j.val + k.val)
  have hp := pow_two_levels hn
  have hpos := Nat.two_pow_pos (n - 2)
  have hv (k : Fin 4) : Edge.tree (v k) ∈ G.edges := by
    apply tree_mem_iff.mpr
    have hs := quad_leaf_spec hn right j k
    exact ⟨hs.1, by simp [v, hs.2.2]⟩
  have hpm (k : Fin 2) : Edge.tree (p k) ∈ G.edges := by
    apply tree_mem_iff.mpr
    have hs := quad_parent_spec hn right j k
    exact ⟨hs.1, by simp [p, hs.2.2]⟩
  have hpar0 : parent n (v 0) = some (p 0) := by
    simpa [v, p] using (quad_leaf_spec hn right j 0).2.2
  have hpar1 : parent n (v 1) = some (p 0) := by
    simpa [v, p] using (quad_leaf_spec hn right j 1).2.2
  have hpar2 : parent n (v 2) = some (p 1) := by
    simpa [v, p] using (quad_leaf_spec hn right j 2).2.2
  have hpar3 : parent n (v 3) = some (p 1) := by
    simpa [v, p] using (quad_leaf_spec hn right j 3).2.2
  have hpp0 : parent n (p 0) = some (heapNode n right (2 ^ (n - 2) - 1 + j.val)) := by
    simpa [p] using (quad_parent_spec hn right j 0).2.2
  have hpp1 : parent n (p 1) = some (heapNode n right (2 ^ (n - 2) - 1 + j.val)) := by
    simpa [p] using (quad_parent_spec hn right j 1).2.2
  have hpn : p 0 ≠ p 1 := by dsimp [p, heapNode]; omega
  have hpc : G.color (.tree (p 0)) ≠ G.color (.tree (p 1)) := by
    apply hG (.tree (p 0)) (hpm 0) (.tree (p 1)) (hpm 1) (by simpa using hpn)
    refine ⟨heapNode n right (2 ^ (n - 2) - 1 + j.val), Or.inr ?_, Or.inr ?_⟩ <;>
      simp [Edge.head, hpp0, hpp1]
  by_cases hc : G.color (.tree (p 0)) ≠ α
  · have hh := child_color_of_parent_ne hG (p 0) (v 0) (v 1) (hpm 0) (hv 0) (hv 1)
      (by dsimp [p, v, heapNode]; omega) (by dsimp [p, v, heapNode]; omega)
      (by dsimp [v, heapNode]; omega) hpar0 hpar1 α hc
    rcases hh with hh | hh
    · exact ⟨0, hh⟩
    · exact ⟨1, hh⟩
  · have hc' : G.color (.tree (p 1)) ≠ α := by
      intro hh
      exact hpc ((not_ne_iff.mp hc).trans hh.symm)
    have hh := child_color_of_parent_ne hG (p 1) (v 2) (v 3) (hpm 1) (hv 2) (hv 3)
      (by dsimp [p, v, heapNode]; omega) (by dsimp [p, v, heapNode]; omega)
      (by dsimp [v, heapNode]; omega) hpar2 hpar3 α hc'
    rcases hh with hh | hh
    · exact ⟨2, hh⟩
    · exact ⟨3, hh⟩

theorem tree_class_card_ge {n l : ℕ} {G : WeldedInstance n}
    (hG : G.IsProperColoring) (hn : 2 ≤ n) (right : Bool)
    (hmid : n - l ≤ heapCol n right n ∧ heapCol n right n ≤ n + l)
    (α : Fin 3) :
    2 ^ (n - 2) ≤ (G.classEdges l (.tr (heapCol n right n) α)).card := by
  choose k hk using fun j : Fin (2 ^ (n - 2)) => leaf_quad_has_color hG hn right j α
  let v (j : Fin (2 ^ (n - 2))) := heapNode n right (2 ^ n - 1 + 4 * j.val + (k j).val)
  have hm (j : Fin (2 ^ (n - 2))) :
      Edge.tree (v j) ∈ G.classEdges l (.tr (heapCol n right n) α) := by
    have hs := quad_leaf_spec hn right j (k j)
    refine Finset.mem_filter.mpr ⟨tree_mem_iff.mpr ⟨hs.1, ?_⟩, ?_⟩
    · simp [v, hs.2.2]
    · change G.bEdge l (.tree (v j)) = some (.tr (heapCol n right n) α)
      simp only [WeldedInstance.bEdge]
      change (if n - l ≤ col n (v j) ∧ col n (v j) ≤ n + l then
        some (EdgeClass.tr (col n (v j)) (G.color (.tree (v j)))) else none) = _
      rw [show col n (v j) = heapCol n right n from hs.2.1, if_pos hmid]
      exact congrArg (fun c => some (EdgeClass.tr (heapCol n right n) c)) (hk j)
  let F : Fin (2 ^ (n - 2)) → G.classEdges l (.tr (heapCol n right n) α) :=
    fun j => ⟨.tree (v j), hm j⟩
  have hinj : Function.Injective F := by
    intro j j' heq
    have hv : v j = v j' := Edge.tree.inj (congrArg Subtype.val heq)
    have hj := (k j).isLt
    have hj' := (k j').isLt
    dsimp [v, heapNode] at hv
    apply Fin.ext
    omega
  simpa only [Fintype.card_fin, Fintype.card_coe] using Fintype.card_le_of_injective F hinj

theorem left_class_card_ge {n l : ℕ} {G : WeldedInstance n}
    (hG : G.IsProperColoring) (hn : 2 ≤ n) (α : Fin 3) :
    2 ^ (n - 2) ≤ (G.classEdges l (.tr n α)).card := by
  exact tree_class_card_ge hG hn false ⟨Nat.sub_le n l, Nat.le_add_right n l⟩ α

theorem right_class_card_ge {n l : ℕ} {G : WeldedInstance n}
    (hG : G.IsProperColoring) (hn : 2 ≤ n) (hl : 1 ≤ l) (α : Fin 3) :
    2 ^ (n - 2) ≤ (G.classEdges l (.tr (n + 1) α)).card := by
  have hc : heapCol n true n = n + 1 := by unfold heapCol; simp only [if_true]; omega
  have hh := tree_class_card_ge (l := l) hG hn true (by rw [hc]; constructor <;> omega) α
  simpa only [hc] using hh

theorem reciprocal_le_four_dyadic {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ^ (n - 2) ≤ m) :
    1 / (m : ℝ) ≤ 4 / (2 : ℝ) ^ n := by
  have hmp : 0 < (m : ℝ) := by
    exact_mod_cast (Nat.lt_of_lt_of_le (Nat.two_pow_pos (n - 2)) hm)
  apply (div_le_div_iff₀ hmp (by positivity : (0 : ℝ) < 2 ^ n)).mpr
  simp only [one_mul]
  have hp : 2 ^ n ≤ 4 * m := by
    rw [(pow_two_levels hn).1]
    exact Nat.mul_le_mul_left 4 hm
  exact_mod_cast hp

theorem left_class_reciprocal_le {n l : ℕ} {G : WeldedInstance n}
    (hG : G.IsProperColoring) (hn : 2 ≤ n) (α : Fin 3) :
    1 / ((G.classEdges l (.tr n α)).card : ℝ) ≤ 4 / (2 : ℝ) ^ n :=
  reciprocal_le_four_dyadic hn (left_class_card_ge hG hn α)

theorem right_class_reciprocal_le {n l : ℕ} {G : WeldedInstance n}
    (hG : G.IsProperColoring) (hn : 2 ≤ n) (hl : 1 ≤ l) (α : Fin 3) :
    1 / ((G.classEdges l (.tr (n + 1) α)).card : ℝ) ≤ 4 / (2 : ℝ) ^ n :=
  reciprocal_le_four_dyadic hn (right_class_card_ge hG hn hl α)

end WeldedPath.NearWeldClasses

end

-- Solutions.WeldedPathFirstFreeStep
section

namespace WeldedPath.Supplement.FirstFreeStep

open Classical WeldedInstance LoopProof NearWeldClasses KappaKernel

variable {n l : ℕ} {G : WeldedInstance n}

theorem tree_head_not_weld {w : ℕ} (he : Edge.tree w ∈ G.edges) :
    col n ((Edge.tree w).head n) ≠ n ∧ col n ((Edge.tree w).head n) ≠ n + 1 := by
  have hm := tree_mem_iff.mp he
  cases hp : parent n w with
  | none => simp [hp] at hm
  | some p =>
    have hs := (parent_spec hp).2.2
    simp only [Edge.head, hp, Option.getD_some]
    constructor <;> intro hc <;> rcases hs with hs | hs <;> omega

/-- At a weld vertex, an incident permuted edge belongs to one of exactly
three kinds of class: the left leaf-tree class, the right leaf-tree class,
or a weld class. -/
theorem class_of_incident_weld {u : ℕ} {e : Edge} {b : EdgeClass}
    (he : e ∈ G.classEdges l b) (hi : e.Incident n u) (hu : u ∈ Vweld n) :
    b = .tr n (G.color e) ∨ b = .tr (n + 1) (G.color e) ∨ b = .wld (G.color e) := by
  have he' := Finset.mem_filter.mp he
  have hu' := (Finset.mem_filter.mp hu).2
  cases e with
  | weld a c =>
    exact Or.inr (Or.inr (Option.some.inj he'.2.symm))
  | tree w =>
    have hc : col n w = n ∨ col n w = n + 1 := by
      rcases hi with hi | hi
      · change u = w at hi
        simpa only [hi] using hu'
      · have hne := tree_head_not_weld he'.1
        change u = (Edge.tree w).head n at hi
        rw [hi] at hu'
        exact (hu'.elim hne.1 hne.2).elim
    have hb : b = .tr (col n w) (G.color (.tree w)) := by
      have hh := he'.2
      simp only [WeldedInstance.bEdge] at hh
      split at hh
      · exact Option.some.inj hh.symm
      · simp at hh
    rcases hc with hc | hc
    · exact Or.inl (by simpa only [hc] using hb)
    · exact Or.inr (Or.inl (by simpa only [hc] using hb))

theorem class_card_ge_of_incident_weld (hG : G.IsValid) (hn : 2 ≤ n) (hl : 1 ≤ l)
    {u : ℕ} {e : Edge} {b : EdgeClass}
    (he : e ∈ G.classEdges l b) (hi : e.Incident n u) (hu : u ∈ Vweld n) :
    2 ^ (n - 2) ≤ (G.classEdges l b).card := by
  rcases class_of_incident_weld he hi hu with hb | hb | hb
  · rw [hb]
    exact left_class_card_ge hG.2 hn (G.color e)
  · rw [hb]
    exact right_class_card_ge hG.2 hn hl (G.color e)
  · rw [hb]
    apply le_trans _ (WeldClasses.weld_class_card_ge hG (by omega) (G.color e))
    exact Nat.pow_le_pow_right (by decide) (by omega)

theorem kappa_from_weld_le (hG : G.IsValid) (hn : 2 ≤ n) (hl : 1 ≤ l)
    {u : ℕ} (hu : u ∈ Vweld n) (α : Fin 3) (v : ℕ) :
    kappa l G α u v ≤ 4 / (2 : ℝ) ^ n := by
  cases hpd : permData l G u α with
  | none => simp only [kappa, hpd]; positivity
  | some d =>
    obtain ⟨b, e, t⟩ := d
    have he := KappaKernel.eAlpha_spec (permData_eAlpha hpd)
    have hc := class_card_ge_of_incident_weld hG hn hl e.2 he.2.2 hu
    exact (kappa_le_inv_classSize hpd v).trans (reciprocal_le_four_dyadic hn hc)

theorem kappa_to_weld_le (hG : G.IsValid) (hn : 2 ≤ n) (hl : 1 ≤ l)
    (u : ℕ) (α : Fin 3) {v : ℕ} (hv : v ∈ Vweld n) :
    kappa l G α u v ≤ 4 / (2 : ℝ) ^ n := by
  rw [kappa_symm hG α u v]
  exact kappa_from_weld_le hG hn hl hv α u

end WeldedPath.Supplement.FirstFreeStep

end

-- Solutions.WeldedPathMidPermData
section

namespace WeldedPath.Supplement.MidPermData

open Classical WeldedInstance LoopProof NearWeldClasses KappaKernel

variable {n l : ℕ} {G : WeldedInstance n}

private theorem three_colors_cover (a b c d : Fin 3) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) : d = a ∨ d = b ∨ d = c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> simp_all

theorem color_of_three_incident (hG : G.IsProperColoring) (u : ℕ)
    (e f g : Edge) (he : e ∈ G.edges) (hf : f ∈ G.edges) (hg : g ∈ G.edges)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (hie : e.Incident n u) (hif : f.Incident n u) (hig : g.Incident n u)
    (α : Fin 3) : ∃ a ∈ G.edges, G.color a = α ∧ a.Incident n u := by
  have hcf := hG e he f hf hef ⟨u, hie, hif⟩
  have hcg := hG e he g hg heg ⟨u, hie, hig⟩
  have hcfg := hG f hf g hg hfg ⟨u, hif, hig⟩
  rcases three_colors_cover _ _ _ α hcf hcg hcfg with h | h | h
  · exact ⟨e, he, h.symm, hie⟩
  · exact ⟨f, hf, h.symm, hif⟩
  · exact ⟨g, hg, h.symm, hig⟩

theorem tree_mem_of_nonroot {u : ℕ} (hu : IsVertex n u)
    (hlo : 0 < col n u) (hhi : col n u < 2 * n + 1) : Edge.tree u ∈ G.edges := by
  apply tree_mem_iff.mpr
  refine ⟨hu, ?_⟩
  unfold parent
  split_ifs <;> simp_all <;> omega

theorem color_at_leaf (hG : G.IsValid) {u : ℕ} (hu : IsLeaf n u)
    (ht : Edge.tree u ∈ G.edges) (α : Fin 3) :
    ∃ e ∈ G.edges, G.color e = α ∧ e.Incident n u := by
  obtain ⟨p, q, hpq, hs⟩ := Finset.card_eq_two.mp (hG.1.2.1 u hu)
  have hp : p ∈ G.weld ∧ (p.1 = u ∨ p.2 = u) := by
    apply Finset.mem_filter.mp
    rw [hs]
    simp
  have hq : q ∈ G.weld ∧ (q.1 = u ∨ q.2 = u) := by
    apply Finset.mem_filter.mp
    rw [hs]
    simp
  have hep : Edge.weld p.1 p.2 ∈ G.edges := weld_mem_iff.mpr hp.1
  have heq : Edge.weld q.1 q.2 ∈ G.edges := weld_mem_iff.mpr hq.1
  have hip : (Edge.weld p.1 p.2).Incident n u := by
    rcases hp.2 with h | h
    · exact Or.inl h.symm
    · exact Or.inr h.symm
  have hiq : (Edge.weld q.1 q.2).Incident n u := by
    rcases hq.2 with h | h
    · exact Or.inl h.symm
    · exact Or.inr h.symm
  have hpq' : Edge.weld p.1 p.2 ≠ Edge.weld q.1 q.2 := by
    intro h
    exact hpq (Prod.ext (congrArg Edge.tail h) (congrArg (Edge.head n) h))
  exact color_of_three_incident hG.2 u (.tree u) (.weld p.1 p.2) (.weld q.1 q.2)
    ht hep heq (by simp) (by simp) hpq' (Or.inl rfl) hip hiq α

theorem color_at_heap_internal (hG : G.IsProperColoring) (right : Bool)
    {d w : ℕ} (hd : 1 ≤ d) (hdn : d < n)
    (hlo : 2 ^ d - 1 ≤ w) (hhi : w < 2 ^ (d + 1) - 1) (α : Fin 3) :
    ∃ e ∈ G.edges, G.color e = α ∧ e.Incident n (heapNode n right w) := by
  have hw := heap_node_spec right hd (Nat.le_of_lt hdn) hlo hhi
  have hdp := Nat.two_pow_pos d
  have hds : 2 ^ (d + 1) = 2 * 2 ^ d := by rw [pow_succ, Nat.mul_comm]
  have hds' : 2 ^ (d + 1 + 1) = 2 * 2 ^ (d + 1) := by rw [pow_succ, Nat.mul_comm]
  have ha := heap_node_spec (n := n) (d := d + 1) (u := 2 * w + 1)
    right (by omega) (by omega) (by omega) (by omega)
  have hb := heap_node_spec (n := n) (d := d + 1) (u := 2 * w + 2)
    right (by omega) (by omega) (by omega) (by omega)
  have hpa : parent n (heapNode n right (2 * w + 1)) = some (heapNode n right w) := by
    simpa only [show (2 * w + 1 - 1) / 2 = w by omega] using ha.2.2
  have hpb : parent n (heapNode n right (2 * w + 2)) = some (heapNode n right w) := by
    simpa only [show (2 * w + 2 - 1) / 2 = w by omega] using hb.2.2
  have hwE : Edge.tree (heapNode n right w) ∈ G.edges :=
    tree_mem_iff.mpr ⟨hw.1, by simp [hw.2.2]⟩
  have haE : Edge.tree (heapNode n right (2 * w + 1)) ∈ G.edges :=
    tree_mem_iff.mpr ⟨ha.1, by simp [hpa]⟩
  have hbE : Edge.tree (heapNode n right (2 * w + 2)) ∈ G.edges :=
    tree_mem_iff.mpr ⟨hb.1, by simp [hpb]⟩
  apply color_of_three_incident hG (heapNode n right w)
    (.tree (heapNode n right w)) (.tree (heapNode n right (2 * w + 1)))
    (.tree (heapNode n right (2 * w + 2))) hwE haE hbE
  · simp only [ne_eq, Edge.tree.injEq, heapNode]
    omega
  · simp only [ne_eq, Edge.tree.injEq, heapNode]
    omega
  · simp only [ne_eq, Edge.tree.injEq, heapNode]
    omega
  · exact Or.inl rfl
  · exact Or.inr (by simp [Edge.head, hpa])
  · exact Or.inr (by simp [Edge.head, hpb])

theorem color_at_nonroot (hG : G.IsValid) {u : ℕ} (hu : IsVertex n u)
    (hlo : 0 < col n u) (hhi : col n u < 2 * n + 1) (α : Fin 3) :
    ∃ e ∈ G.edges, G.color e = α ∧ e.Incident n u := by
  by_cases hleaf : col n u = n ∨ col n u = n + 1
  · exact color_at_leaf hG ⟨hu, hleaf⟩ (tree_mem_of_nonroot hu hlo hhi) α
  · by_cases hleft : u < 2 ^ (n + 1) - 1
    · let d := Nat.log 2 (u + 1)
      have hc : col n u = d := by simp [col, hleft, d]
      have hd : 1 ≤ d := by omega
      have hdn : d < n := by
        have hh := log_left_le n u hleft
        dsimp [d]
        omega
      have hlow := Nat.pow_log_le_self 2 (by omega : u + 1 ≠ 0)
      have hupp := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (u + 1)
      have hh := color_at_heap_internal (w := u) hG.2 false hd hdn
        (by dsimp [d]; omega) (by dsimp [d]; omega) α
      simpa only [heapNode, Bool.false_eq_true, if_false, zero_add] using hh
    · let R := 2 ^ (n + 1) - 1
      let w := u - R
      let d := Nat.log 2 (w + 1)
      have hR : R ≤ u := by dsimp [R]; omega
      have heq : heapNode n true w = u := by dsimp [heapNode, w]; omega
      have hc : col n u = 2 * n + 1 - d := by
        simp only [col, if_neg hleft]
        rfl
      have hdnle : d ≤ n := log_right_le n u hu hR
      have hd : 1 ≤ d := by omega
      have hdn : d < n := by omega
      have hlow := Nat.pow_log_le_self 2 (by omega : w + 1 ≠ 0)
      have hupp := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (w + 1)
      have hh := color_at_heap_internal (w := w) hG.2 true hd hdn
        (by dsimp [d]; omega) (by dsimp [d]; omega) α
      simpa only [heq] using hh

theorem incident_mid_class (hG : G.IsValid) {u : ℕ} {e : Edge}
    (he : e ∈ G.edges) (hi : e.Incident n u) (hu : u ∈ Vmid n l) :
    ∃ b : PClass n l, e ∈ G.classEdges l b.1 := by
  have hum := (Finset.mem_filter.mp hu).2
  cases e with
  | tree w =>
    have hadj := (edge_endpoints hG he).2.2
    have hm : n - l ≤ col n w ∧ col n w ≤ n + l := by
      rcases hi with hi | hi
      · change u = w at hi
        rw [hi] at hum
        omega
      · change u = (Edge.tree w).head n at hi
        rw [hi] at hum
        change col n w + 1 = col n ((Edge.tree w).head n) ∨
          col n ((Edge.tree w).head n) + 1 = col n w at hadj
        omega
    let b : PClass n l := ⟨.tr (col n w) (G.color (.tree w)), by simp [BEdge, hm]; omega⟩
    refine ⟨b, Finset.mem_filter.mpr ⟨he, ?_⟩⟩
    simp [b, WeldedInstance.bEdge, hm]
  | weld a c =>
    let b : PClass n l := ⟨.wld (G.color (.weld a c)), by simp [BEdge]⟩
    exact ⟨b, Finset.mem_filter.mpr ⟨he, rfl⟩⟩

theorem permData_ne_none_of_mem_Vmid (hG : G.IsValid) (hn : 16 ≤ n)
    (hl : 2 ≤ l) (hln : l ≤ n - 4) {u : ℕ} (hu : u ∈ Vmid n l) (α : Fin 3) :
    permData l G u α ≠ none := by
  have huv := Finset.mem_filter.mp hu
  have hv : IsVertex n u := Finset.mem_range.mp huv.1
  obtain ⟨e, he, hc, hi⟩ := color_at_nonroot hG hv (by omega) (by omega) α
  obtain ⟨b, hb⟩ := incident_mid_class hG he hi hu
  have hp := permData_of_class_edge hG (⟨e, hb⟩ : G.classEdges l b.1) u hi
  rw [hc] at hp
  rw [hp]
  simp

end WeldedPath.Supplement.MidPermData

end

-- Solutions.WeldedPathKappaWalk
section

namespace WeldedPath.Supplement.KappaWalk

open WeldedInstance KappaKernel
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}

lemma class_tail_injective (hG : G.IsProperColoring) (b : PClass n l) :
    Set.InjOn Edge.tail (G.classEdges l b.1) := by
  intro e he e' he' htail
  by_contra hne
  exact (hG e (Finset.mem_filter.mp he).1 e' (Finset.mem_filter.mp he').1 hne
    ⟨e.tail, Or.inl rfl, Or.inl htail⟩) (class_color he he')

lemma class_head_injective (hG : G.IsProperColoring) (b : PClass n l) :
    Set.InjOn (Edge.head n) (G.classEdges l b.1) := by
  intro e he e' he' hhead
  by_contra hne
  exact (hG e (Finset.mem_filter.mp he).1 e' (Finset.mem_filter.mp he').1 hne
    ⟨e.head n, Or.inr rfl, Or.inr hhead⟩) (class_color he he')

lemma vertex_lt_label (hn : 2 ≤ n) {v : ℕ} (hv : IsVertex n v) :
    v < labelBound n + 1 := by
  have hp : 2 ^ (n + 2) ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by omega) (by omega)
  unfold IsVertex numV at hv
  unfold labelBound
  omega

lemma sum_uniform_label_eq_one (S : Finset ℕ) (m : ℕ)
    (hc : S.card = m) (hm : 0 < m) (hS : ∀ v ∈ S, v < labelBound n + 1) :
    (∑ v : Label n, if v.1 ∈ S then 1 / (m : ℝ) else 0) = 1 := by
  classical
  have hcard : (Finset.univ.filter fun v : Label n => v.1 ∈ S).card = S.card := by
    apply Finset.card_bij (fun v _ => v.1)
    · intro v hv
      exact (Finset.mem_filter.mp hv).2
    · intro v hv w hw h
      exact Fin.ext h
    · intro v hv
      exact ⟨⟨v, hS v hv⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩, rfl⟩
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, hcard, hc]
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  field_simp

lemma kappa_label_row_sum_eq_one (hG : G.IsValid) (hn : 2 ≤ n)
    {u : ℕ} {α : Fin 3} {b : PClass n l} {e : ↥(G.classEdges l b.1)} {t : Bool}
    (hpd : permData l G u α = some ⟨b, e, t⟩) :
    (∑ v : Label n, kappa l G α u v.1) = 1 := by
  classical
  have hm : 0 < classSize l G b := Finset.card_pos.mpr ⟨e.1, e.2⟩
  cases t
  · simpa only [kappa, hpd, Bool.false_eq_true, false_and, true_and, false_or] using
      sum_uniform_label_eq_one ((G.classEdges l b.1).image Edge.tail) (classSize l G b)
        (Finset.card_image_iff.mpr (class_tail_injective hG.2 b)) hm (by
          intro v hv
          obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hv
          exact vertex_lt_label hn (LoopProof.edge_endpoints hG (Finset.mem_filter.mp hf).1).1)
  · simpa only [kappa, hpd, Bool.true_eq_false, false_and, true_and, or_false] using
      sum_uniform_label_eq_one ((G.classEdges l b.1).image (Edge.head n)) (classSize l G b)
        (Finset.card_image_iff.mpr (class_head_injective hG.2 b)) hm (by
          intro v hv
          obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hv
          exact vertex_lt_label hn (LoopProof.edge_endpoints hG (Finset.mem_filter.mp hf).1).2.1)

lemma mem_region_of_col {v : ℕ} (hv : IsVertex n v)
    (hlo : n - l - 1 ≤ col n v) (hhi : col n v ≤ n + l + 1) :
    v ∈ Vmid n l ∪ Vbd n l := by
  by_cases hm : n - l < col n v ∧ col n v < n + l
  · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hv, hm⟩))
  · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr hv, by omega⟩))

lemma class_endpoints_region (hG : G.IsValid) {b : PClass n l}
    (e : ↥(G.classEdges l b.1)) :
    e.1.tail ∈ Vmid n l ∪ Vbd n l ∧ e.1.head n ∈ Vmid n l ∪ Vbd n l := by
  have he := Finset.mem_filter.mp e.2
  have hend := LoopProof.edge_endpoints hG he.1
  obtain ⟨e, hem⟩ := e
  cases e with
  | tree v =>
    dsimp only at he hend ⊢
    have hc : n - l ≤ col n v ∧ col n v ≤ n + l := by
      by_contra h
      have hb := he.2
      simp only [WeldedInstance.bEdge, if_neg h] at hb
      cases hb
    simp only [Edge.tail] at hend ⊢
    constructor
    · apply mem_region_of_col hend.1 <;> omega
    · apply mem_region_of_col hend.2.1 <;> rcases hend.2.2 with h | h <;> omega
  | weld u v =>
    dsimp only at he hend ⊢
    have hw := hG.1.1 (u, v) (LoopProof.weld_mem_iff.mp he.1)
    dsimp only at hw
    simp only [Edge.tail, Edge.head] at hend ⊢
    constructor
    · apply mem_region_of_col hend.1 <;> omega
    · apply mem_region_of_col hend.2.1 <;> omega

lemma kappa_output_region (hG : G.IsValid) {α : Fin 3} {u v : ℕ}
    (hk : kappa l G α u v ≠ 0) : v ∈ Vmid n l ∪ Vbd n l := by
  classical
  cases hpd : permData l G u α with
  | none => simp [kappa, hpd] at hk
  | some d =>
    obtain ⟨b, e, t⟩ := d
    have hm : (t = true ∧ v ∈ (G.classEdges l b.1).image (Edge.head n)) ∨
        (t = false ∧ v ∈ (G.classEdges l b.1).image Edge.tail) := by
      by_contra hh
      exact hk (by simp only [kappa, hpd, if_neg hh])
    rcases hm with ⟨_, hv⟩ | ⟨_, hv⟩
    · obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp hv
      exact (class_endpoints_region hG ⟨e', he'⟩).2
    · obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp hv
      exact (class_endpoints_region hG ⟨e', he'⟩).1

lemma kappa_zero_outside_region (hG : G.IsValid) (α : Fin 3) (u v : ℕ)
    (hv : v ∉ Vmid n l ∪ Vbd n l) : kappa l G α u v = 0 := by
  by_contra h
  exact hv (kappa_output_region hG h)

noncomputable def step (l : ℕ) (G : WeldedInstance n) (α : Fin 3)
    (p : Label n → ℝ) : Label n → ℝ := fun y =>
  ∑ x : Label n, p x * kappa l G α x.1 y.1

noncomputable def walk (l : ℕ) (G : WeldedInstance n) :
    List (Fin 3) → (Label n → ℝ) → (Label n → ℝ)
  | [], p => p
  | α :: cs, p => walk l G cs (step l G α p)

lemma walk_nonneg (l : ℕ) (G : WeldedInstance n) (cs : List (Fin 3))
    (p : Label n → ℝ) (hp : ∀ x, 0 ≤ p x) : ∀ x, 0 ≤ walk l G cs p x := by
  induction cs generalizing p with
  | nil => exact hp
  | cons α cs ih =>
    exact ih (step l G α p) (fun x => kappa_step_nonneg l G α p hp x.1)

lemma walk_point_bound (hG : G.IsValid) (cs : List (Fin 3))
    (p : Label n → ℝ) (M : ℝ) (hM : 0 ≤ M) (hp : ∀ x, p x ≤ M) :
    ∀ x, walk l G cs p x ≤ M := by
  induction cs generalizing p with
  | nil => exact hp
  | cons α cs ih =>
    exact ih (step l G α p) (fun x => kappa_propagates_point_bound hG α p M hM hp x.1)

lemma walk_abs_bound (hG : G.IsValid) (cs : List (Fin 3))
    (p : Label n → ℝ) (M : ℝ) (hM : 0 ≤ M) (hp : ∀ x, |p x| ≤ M) :
    ∀ x, |walk l G cs p x| ≤ M := by
  induction cs generalizing p with
  | nil => exact hp
  | cons α cs ih =>
    exact ih (step l G α p) (fun x => kappa_propagates_abs_bound hG α p M hM hp x.1)

lemma walk_mass_le (l : ℕ) (G : WeldedInstance n) (cs : List (Fin 3))
    (p : Label n → ℝ) (hp : ∀ x, 0 ≤ p x) :
    (∑ x, walk l G cs p x) ≤ ∑ x, p x := by
  induction cs generalizing p with
  | nil => exact le_rfl
  | cons α cs ih =>
    exact (ih (step l G α p) (fun x => kappa_step_nonneg l G α p hp x.1)).trans
      (kappa_step_mass_le l G α p hp)

noncomputable def kill (B : Finset ℕ) (p : Label n → ℝ) : Label n → ℝ :=
  fun x => if x.1 ∈ B then 0 else p x

noncomputable def safeWalk (l : ℕ) (G : WeldedInstance n) (B : Finset ℕ) :
    List (Fin 3) → (Label n → ℝ) → (Label n → ℝ)
  | [], p => kill B p
  | α :: cs, p => safeWalk l G B cs (step l G α (kill B p))

lemma kill_nonneg (B : Finset ℕ) (p : Label n → ℝ) (hp : ∀ x, 0 ≤ p x) :
    ∀ x, 0 ≤ kill B p x := by
  intro x
  unfold kill
  split
  · exact le_rfl
  · exact hp x

lemma kill_point_bound (B : Finset ℕ) (p : Label n → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hp : ∀ x, p x ≤ M) : ∀ x, kill B p x ≤ M := by
  intro x
  unfold kill
  split
  · exact hM
  · exact hp x

lemma kill_mass_loss (B : Finset ℕ) (p : Label n → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hp : ∀ x, p x ≤ M) :
    (∑ x, p x) - (B.card : ℝ) * M ≤ ∑ x, kill B p x := by
  classical
  let T := Finset.univ.filter fun x : Label n => x.1 ∈ B
  have hcard : T.card ≤ B.card := Finset.card_le_card_of_injOn Fin.val
    (fun x hx => (Finset.mem_filter.mp hx).2)
    (fun _ _ _ _ h => Fin.ext h)
  have hbad : (∑ x : Label n, if x.1 ∈ B then p x else 0) ≤ (B.card : ℝ) * M := by
    calc
      _ ≤ ∑ x : Label n, if x.1 ∈ B then M else 0 := by
        apply Finset.sum_le_sum
        intro x _
        split_ifs
        · exact hp x
        · exact le_rfl
      _ = (T.card : ℝ) * M := by
        rw [← Finset.sum_filter]
        simp [T]
      _ ≤ (B.card : ℝ) * M := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hM
  have hid : (∑ x, p x) = (∑ x, kill B p x) + ∑ x, if x.1 ∈ B then p x else 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    unfold kill
    split_ifs <;> simp
  linarith

lemma safeWalk_nonneg (l : ℕ) (G : WeldedInstance n) (B : Finset ℕ)
    (cs : List (Fin 3)) (p : Label n → ℝ) (hp : ∀ x, 0 ≤ p x) :
    ∀ x, 0 ≤ safeWalk l G B cs p x := by
  induction cs generalizing p with
  | nil => exact kill_nonneg B p hp
  | cons α cs ih =>
    exact ih _ (fun x => kappa_step_nonneg l G α _ (kill_nonneg B p hp) x.1)

lemma safeWalk_point_bound (hG : G.IsValid) (B : Finset ℕ) (cs : List (Fin 3))
    (p : Label n → ℝ) (M : ℝ) (hM : 0 ≤ M) (hp : ∀ x, p x ≤ M) :
    ∀ x, safeWalk l G B cs p x ≤ M := by
  induction cs generalizing p with
  | nil => exact kill_point_bound B p M hM hp
  | cons α cs ih =>
    exact ih _ (fun x => kappa_propagates_point_bound hG α _ M hM
      (kill_point_bound B p M hM hp) x.1)

lemma step_mass_eq_of_support (α : Fin 3) (p : Label n → ℝ) (S : Finset ℕ)
    (hp : ∀ x, x.1 ∉ S → p x = 0)
    (hrow : ∀ x : Label n, x.1 ∈ S → (∑ y : Label n, kappa l G α x.1 y.1) = 1) :
    (∑ x, step l G α p x) = ∑ x, p x := by
  unfold step
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [← Finset.mul_sum]
  by_cases hx : x.1 ∈ S
  · rw [hrow x hx, mul_one]
  · rw [hp x hx, zero_mul]

lemma safeWalk_mass_lower (hG : G.IsValid) (S B : Finset ℕ)
    (hstay : ∀ α : Fin 3, ∀ x y : Label n, y.1 ∉ S → kappa l G α x.1 y.1 = 0)
    (hrow : ∀ α : Fin 3, ∀ x : Label n, x.1 ∈ S → x.1 ∉ B →
      (∑ y : Label n, kappa l G α x.1 y.1) = 1)
    (cs : List (Fin 3)) (p : Label n → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hp : ∀ x, p x ≤ M) (hsupp : ∀ x, x.1 ∉ S → p x = 0) :
    (∑ x, p x) - ((cs.length + 1 : ℕ) : ℝ) * (B.card : ℝ) * M ≤
      ∑ x, safeWalk l G B cs p x := by
  classical
  induction cs generalizing p with
  | nil => simpa [safeWalk] using kill_mass_loss B p M hM hp
  | cons α cs ih =>
    have hcap : ∀ x, step l G α (kill B p) x ≤ M :=
      fun x => kappa_propagates_point_bound hG α _ M hM
        (kill_point_bound B p M hM hp) x.1
    have hs : ∀ x, x.1 ∉ S → step l G α (kill B p) x = 0 := by
      intro y hy
      unfold step
      apply Finset.sum_eq_zero
      intro x _
      rw [hstay α x y hy, mul_zero]
    have heq : (∑ x, step l G α (kill B p) x) = ∑ x, kill B p x := by
      apply step_mass_eq_of_support α _ (S \ B)
      · intro x hx
        by_cases hb : x.1 ∈ B
        · simp [kill, hb]
        · have hns : x.1 ∉ S := by simpa [Finset.mem_sdiff, hb] using hx
          simp [kill, hb, hsupp x hns]
      · intro x hx
        exact hrow α x (Finset.mem_sdiff.mp hx).1 (Finset.mem_sdiff.mp hx).2
    have hi := ih _ hcap hs
    have hloss := kill_mass_loss B p M hM hp
    rw [heq] at hi
    simp only [safeWalk, List.length_cons, Nat.cast_add, Nat.cast_one] at *
    nlinarith

lemma safeWalk_conditioned_point_bound (hG : G.IsValid) (B : Finset ℕ)
    (cs : List (Fin 3)) (p : Label n → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hp : ∀ x, p x ≤ M)
    (hsurv : (1 / 2 : ℝ) ≤ ∑ x, safeWalk l G B cs p x) (y : Label n) :
    safeWalk l G B cs p y / (∑ x, safeWalk l G B cs p x) ≤ 2 * M := by
  have hz : 0 < ∑ x, safeWalk l G B cs p x := by linarith
  apply (div_le_iff₀ hz).mpr
  have hy := safeWalk_point_bound (l := l) hG B cs p M hM hp y
  nlinarith

lemma kappa_mid_row_sum_eq_one (hG : G.IsValid) (hn : 16 ≤ n)
    (hl : 2 ≤ l) (hln : l ≤ n - 4) {u : ℕ} (hu : u ∈ Vmid n l) (α : Fin 3) :
    (∑ y : Label n, kappa l G α u y.1) = 1 := by
  have hne := MidPermData.permData_ne_none_of_mem_Vmid hG hn hl hln hu α
  cases hpd : permData l G u α with
  | none => exact False.elim (hne hpd)
  | some d =>
    obtain ⟨b, e, t⟩ := d
    exact kappa_label_row_sum_eq_one hG (by omega) hpd

lemma weld_mem_mid (hn : 16 ≤ n) (hl : 2 ≤ l) (hln : l ≤ n - 4)
    {u : ℕ} (hu : u ∈ Vweld n) : u ∈ Vmid n l := by
  obtain ⟨hv, hc⟩ := Finset.mem_filter.mp hu
  exact Finset.mem_filter.mpr ⟨hv, by rcases hc with hc | hc <;> omega⟩

lemma kappa_weld_row_sum_eq_one (hG : G.IsValid) (hn : 16 ≤ n)
    (hl : 2 ≤ l) (hln : l ≤ n - 4) {u : ℕ} (hu : u ∈ Vweld n) (α : Fin 3) :
    (∑ y : Label n, kappa l G α u y.1) = 1 :=
  kappa_mid_row_sum_eq_one hG hn hl hln (weld_mem_mid hn hl hln hu) α

lemma safeWalk_region_mass_lower (hG : G.IsValid) (hn : 16 ≤ n)
    (hl : 2 ≤ l) (hln : l ≤ n - 4) (B : Finset ℕ) (hB : Vbd n l ⊆ B)
    (cs : List (Fin 3)) (p : Label n → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hp : ∀ x, p x ≤ M)
    (hsupp : ∀ x, x.1 ∉ Vmid n l ∪ Vbd n l → p x = 0) :
    (∑ x, p x) - ((cs.length + 1 : ℕ) : ℝ) * (B.card : ℝ) * M ≤
      ∑ x, safeWalk l G B cs p x := by
  apply safeWalk_mass_lower hG (Vmid n l ∪ Vbd n l) B
    (fun α x y hy => kappa_zero_outside_region hG α x.1 y.1 hy) _ cs p M hM hp hsupp
  intro α x hx hb
  have hmid : x.1 ∈ Vmid n l := (Finset.mem_union.mp hx).resolve_right (fun h => hb (hB h))
  exact kappa_mid_row_sum_eq_one hG hn hl hln hmid α

lemma safeWalk_region_normalized_bound (hG : G.IsValid) (hn : 16 ≤ n)
    (hl : 2 ≤ l) (hln : l ≤ n - 4) (B : Finset ℕ) (hB : Vbd n l ⊆ B)
    (cs : List (Fin 3)) (p : Label n → ℝ)
    (hp : ∀ x, p x ≤ 4 / (2 : ℝ) ^ n) (hmass : (∑ x, p x) = 1)
    (hsupp : ∀ x, x.1 ∉ Vmid n l ∪ Vbd n l → p x = 0)
    (hsmall : ((cs.length + 1 : ℕ) : ℝ) * (B.card : ℝ) * (4 / (2 : ℝ) ^ n) ≤ 1 / 2)
    (y : Label n) :
    safeWalk l G B cs p y / (∑ x, safeWalk l G B cs p x) ≤ 8 / (2 : ℝ) ^ n := by
  have hs := safeWalk_region_mass_lower hG hn hl hln B hB cs p _ (by positivity) hp hsupp
  rw [hmass] at hs
  have hsurv : (1 / 2 : ℝ) ≤ ∑ x, safeWalk l G B cs p x := by linarith
  have hb := safeWalk_conditioned_point_bound hG B cs p _ (by positivity) hp hsurv y
  convert hb using 1 <;> ring

end WeldedPath.Supplement.KappaWalk

end

-- Solutions.WeldedPathKappaForest
section

namespace WeldedPath.Supplement.KappaForest

open scoped BigOperators

variable {X : Type*} [Fintype X]
variable {m : ℕ}

noncomputable def prefixLaw (K : (i : ℕ) → (Fin i → X) → X → ℝ) :
    (m : ℕ) → (Fin m → X) → ℝ
  | 0, _ => 1
  | m + 1, z => prefixLaw K m (Fin.init z) * K m (Fin.init z) (z (Fin.last m))

lemma sum_snoc (m : ℕ) (f : (Fin (m + 1) → X) → ℝ) :
    (∑ z, f z) = ∑ p : Fin m → X, ∑ y : X, f (Fin.snoc p y) := by
  classical
  calc
    _ = ∑ q : X × (Fin m → X), f (Fin.snoc q.2 q.1) :=
      Fintype.sum_equiv (Fin.snocEquiv (fun _ : Fin (m + 1) => X)).symm _ _
        (fun z => by simp)
    _ = _ := by rw [Fintype.sum_prod_type, Finset.sum_comm]

omit [Fintype X] in
lemma prefixLaw_snoc (K : (i : ℕ) → (Fin i → X) → X → ℝ)
    (m : ℕ) (p : Fin m → X) (y : X) :
    prefixLaw K (m + 1) (Fin.snoc p y) = prefixLaw K m p * K m p y := by
  simp [prefixLaw]

omit [Fintype X] in
lemma prefixLaw_nonneg (K : (i : ℕ) → (Fin i → X) → X → ℝ)
    (hK : ∀ i p y, 0 ≤ K i p y) (m : ℕ) (z : Fin m → X) :
    0 ≤ prefixLaw K m z := by
  induction m with
  | zero => simp [prefixLaw]
  | succ m ih => exact mul_nonneg (ih _) (hK _ _ _)

def before (z : Fin m → X) (i : Fin m) : Fin i.1 → X :=
  fun j => z ⟨j.1, lt_trans j.2 i.2⟩

omit [Fintype X] in
lemma prefixLaw_eq_prod (K : (i : ℕ) → (Fin i → X) → X → ℝ)
    (m : ℕ) (z : Fin m → X) :
    prefixLaw K m z = ∏ i : Fin m, K i.1 (before z i) (z i) := by
  induction m with
  | zero => simp [prefixLaw]
  | succ m ih =>
    rw [prefixLaw, ih, Fin.prod_univ_castSucc]
    apply congrArg₂ (· * ·)
    · apply Finset.prod_congr rfl
      intro i _
      rfl
    · rfl

lemma prefixLaw_mass_le_one (K : (i : ℕ) → (Fin i → X) → X → ℝ)
    (hK : ∀ i p y, 0 ≤ K i p y) (hrow : ∀ i p, ∑ y, K i p y ≤ 1)
    (m : ℕ) : (∑ z, prefixLaw K m z) ≤ 1 := by
  classical
  induction m with
  | zero => simp [prefixLaw]
  | succ m ih =>
    rw [sum_snoc]
    simp_rw [prefixLaw_snoc]
    calc
      _ = ∑ p, prefixLaw K m p * ∑ y, K m p y := by simp_rw [Finset.mul_sum]
      _ ≤ ∑ p, prefixLaw K m p := Finset.sum_le_sum fun p _ => by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (hrow m p)
          (prefixLaw_nonneg K hK m p)
      _ ≤ 1 := ih

open Classical in
noncomputable def marginal (w : (Fin m → X) → ℝ) (j : Fin m) (x : X) : ℝ :=
  ∑ z, if z j = x then w z else 0

lemma prefixLaw_old_marginal_le (K : (i : ℕ) → (Fin i → X) → X → ℝ)
    (hK : ∀ i p y, 0 ≤ K i p y) (hrow : ∀ i p, ∑ y, K i p y ≤ 1)
    (m : ℕ) (j : Fin m) (x : X) :
    marginal (prefixLaw K (m + 1)) j.castSucc x ≤ marginal (prefixLaw K m) j x := by
  classical
  unfold marginal
  rw [sum_snoc]
  simp only [prefixLaw_snoc, Fin.snoc_castSucc]
  apply Finset.sum_le_sum
  intro p _
  by_cases hpx : p j = x
  · simp only [hpx, if_true]
    rw [← Finset.mul_sum]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (hrow m p)
      (prefixLaw_nonneg K hK m p)
  · simp [hpx]

lemma prefixLaw_new_marginal (K : (i : ℕ) → (Fin i → X) → X → ℝ)
    (m : ℕ) (x : X) :
    marginal (prefixLaw K (m + 1)) (Fin.last m) x =
      ∑ p : Fin m → X, prefixLaw K m p * K m p x := by
  classical
  unfold marginal
  rw [sum_snoc]
  simp [prefixLaw_snoc]

lemma marginal_pushforward (w : (Fin m → X) → ℝ) (j : Fin m) (f : X → ℝ) :
    (∑ p, w p * f (p j)) = ∑ x, marginal w j x * f x := by
  classical
  unfold marginal
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  simp

omit [Fintype X] in
lemma prefixLaw_mono (K L : (i : ℕ) → (Fin i → X) → X → ℝ)
    (hL : ∀ i z y, 0 ≤ L i z y) (hLK : ∀ i z y, L i z y ≤ K i z y)
    (m : ℕ) (z : Fin m → X) : prefixLaw L m z ≤ prefixLaw K m z := by
  induction m with
  | zero => exact le_rfl
  | succ m ih =>
    exact mul_le_mul (ih _) (hLK _ _ _) (hL _ _ _)
      (le_trans (prefixLaw_nonneg L hL m _) (ih _))

lemma marginal_mono (w v : (Fin m → X) → ℝ) (h : ∀ z, w z ≤ v z)
    (j : Fin m) (x : X) : marginal w j x ≤ marginal v j x := by
  classical
  apply Finset.sum_le_sum
  intro z _
  split_ifs
  · exact h z
  · exact le_rfl

open Classical in
noncomputable def maskKernel (K : (i : ℕ) → (Fin i → X) → X → ℝ) (B : Finset X)
    (i : ℕ) (z : Fin i → X) (y : X) : ℝ := if y ∈ B then 0 else K i z y

omit [Fintype X] in
lemma maskKernel_nonneg (K : (i : ℕ) → (Fin i → X) → X → ℝ) (B : Finset X)
    (hK : ∀ i z y, 0 ≤ K i z y) : ∀ i z y, 0 ≤ maskKernel K B i z y := by
  intro i z y
  unfold maskKernel
  split
  · exact le_rfl
  · exact hK i z y

omit [Fintype X] in
lemma maskKernel_le (K : (i : ℕ) → (Fin i → X) → X → ℝ) (B : Finset X)
    (hK : ∀ i z y, 0 ≤ K i z y) : ∀ i z y, maskKernel K B i z y ≤ K i z y := by
  intro i z y
  unfold maskKernel
  split
  · exact hK i z y
  · exact le_rfl

omit [Fintype X] in
lemma masked_prefixLaw_le (K : (i : ℕ) → (Fin i → X) → X → ℝ) (B : Finset X)
    (hK : ∀ i z y, 0 ≤ K i z y) (m : ℕ) (z : Fin m → X) :
    prefixLaw (maskKernel K B) m z ≤ prefixLaw K m z :=
  prefixLaw_mono K _ (maskKernel_nonneg K B hK) (maskKernel_le K B hK) m z

lemma masked_mass_step (K : (i : ℕ) → (Fin i → X) → X → ℝ) (B : Finset X)
    (m : ℕ)
    (hrow : ∀ z, prefixLaw (maskKernel K B) m z ≠ 0 → ∑ y, K m z y = 1) :
    (∑ z, prefixLaw (maskKernel K B) (m + 1) z) =
      (∑ z, prefixLaw (maskKernel K B) m z) -
        ∑ y ∈ B, ∑ z, prefixLaw (maskKernel K B) m z * K m z y := by
  classical
  rw [sum_snoc]
  simp only [prefixLaw_snoc]
  rw [Finset.sum_comm (s := B)]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro z _
  have hz : prefixLaw (maskKernel K B) m z * (∑ y, K m z y) =
      prefixLaw (maskKernel K B) m z := by
    by_cases h : prefixLaw (maskKernel K B) m z = 0
    · simp [h]
    · rw [hrow z h, mul_one]
  have htot : (∑ y, prefixLaw (maskKernel K B) m z * K m z y) =
      prefixLaw (maskKernel K B) m z := by
    rw [← Finset.mul_sum]
    exact hz
  have hid : (∑ y, prefixLaw (maskKernel K B) m z * K m z y) =
      (∑ y, prefixLaw (maskKernel K B) m z * maskKernel K B m z y) +
        ∑ y ∈ B, prefixLaw (maskKernel K B) m z * K m z y := by
    have hb : (∑ y ∈ B, prefixLaw (maskKernel K B) m z * K m z y) =
        ∑ y, if y ∈ B then prefixLaw (maskKernel K B) m z * K m z y else 0 := by
      rw [← Finset.sum_filter]
      simp
    rw [hb]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro y _
    by_cases hy : y ∈ B <;> simp [maskKernel, hy]
  linarith

lemma masked_mass_lower (K : (i : ℕ) → (Fin i → X) → X → ℝ) (B : Finset X)
    (hK : ∀ i z y, 0 ≤ K i z y) (M : ℝ) (m : ℕ)
    (hrow : ∀ i < m, ∀ z, prefixLaw (maskKernel K B) i z ≠ 0 → ∑ y, K i z y = 1)
    (hcap : ∀ i < m, ∀ y, marginal (prefixLaw K (i + 1)) (Fin.last i) y ≤ M) :
    1 - (m : ℝ) * (B.card : ℝ) * M ≤ ∑ z, prefixLaw (maskKernel K B) m z := by
  classical
  induction m with
  | zero => simp [prefixLaw]
  | succ m ih =>
    have ih' := ih (fun i hi => hrow i (by omega)) (fun i hi => hcap i (by omega))
    rw [masked_mass_step K B m (hrow m (Nat.lt_succ_self m))]
    have hb : (∑ y ∈ B, ∑ z, prefixLaw (maskKernel K B) m z * K m z y) ≤
        (B.card : ℝ) * M := by
      calc
        _ ≤ ∑ y ∈ B, marginal (prefixLaw K (m + 1)) (Fin.last m) y := by
          apply Finset.sum_le_sum
          intro y _
          rw [prefixLaw_new_marginal]
          exact Finset.sum_le_sum fun z _ =>
            mul_le_mul_of_nonneg_right (masked_prefixLaw_le K B hK m z) (hK m z y)
        _ ≤ ∑ _y ∈ B, M := Finset.sum_le_sum fun y _ => hcap m (Nat.lt_succ_self m) y
        _ = _ := by simp
    push_cast
    nlinarith

omit [Fintype X] in
lemma prefixLaw_support (K : (i : ℕ) → (Fin i → X) → X → ℝ) (P : X → Prop)
    (hK : ∀ i z y, K i z y ≠ 0 → P y) (m : ℕ) (z : Fin m → X)
    (hz : prefixLaw K m z ≠ 0) : ∀ j, P (z j) := by
  rw [prefixLaw_eq_prod] at hz
  intro j
  exact hK _ _ _ ((Finset.prod_ne_zero_iff.mp hz) j (Finset.mem_univ j))

omit [Fintype X] in
open Classical in
lemma masked_prefixLaw_eq (K : (i : ℕ) → (Fin i → X) → X → ℝ) (B : Finset X)
    (m : ℕ) (z : Fin m → X) :
    prefixLaw (maskKernel K B) m z =
      if ∀ j, z j ∉ B then prefixLaw K m z else 0 := by
  classical
  by_cases h : ∀ j, z j ∉ B
  · rw [if_pos h]
    simp only [prefixLaw_eq_prod]
    apply Finset.prod_congr rfl
    intro j _
    exact if_neg (h j)
  · rw [if_neg h, prefixLaw_eq_prod]
    obtain ⟨j, hj⟩ := not_forall.mp h
    have hj' : z j ∈ B := not_not.mp hj
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [maskKernel, hj'])

variable {n l : ℕ} {G : WeldedInstance n}

noncomputable def forestKernel (l : ℕ) (G : WeldedInstance n)
    (parent : (i : ℕ) → Option (Fin i)) (root : ℕ → Label n) (color : ℕ → Fin 3)
    (i : ℕ) (z : Fin i → Label n) (y : Label n) : ℝ :=
  kappa l G (color i) (match parent i with | none => (root i).1 | some j => (z j).1) y.1

lemma forestKernel_nonneg (l : ℕ) (G : WeldedInstance n)
    (parent : (i : ℕ) → Option (Fin i)) (root : ℕ → Label n) (color : ℕ → Fin 3)
    (i : ℕ) (z : Fin i → Label n) (y : Label n) :
    0 ≤ forestKernel l G parent root color i z y :=
  KappaKernel.kappa_nonneg _ _ _ _ _

lemma forestKernel_row_le (l : ℕ) (G : WeldedInstance n)
    (parent : (i : ℕ) → Option (Fin i)) (root : ℕ → Label n) (color : ℕ → Fin 3)
    (i : ℕ) (z : Fin i → Label n) :
    (∑ y, forestKernel l G parent root color i z y) ≤ 1 :=
  KappaKernel.kappa_label_row_sum_le_one _ _ _ _

lemma forestLaw_marginal_cap (hG : G.IsValid) (hn : 2 ≤ n) (hl : 1 ≤ l)
    (parent : (i : ℕ) → Option (Fin i)) (root : ℕ → Label n) (color : ℕ → Fin 3)
    (m : ℕ) (hroot : ∀ i < m, parent i = none → (root i).1 ∈ Vweld n) :
    ∀ (j : Fin m) (y : Label n),
      marginal (prefixLaw (forestKernel l G parent root color) m) j y ≤ 4 / (2 : ℝ) ^ n := by
  classical
  let K := forestKernel l G parent root color
  have hK : ∀ i z y, 0 ≤ K i z y := forestKernel_nonneg l G parent root color
  have hrow : ∀ i z, ∑ y, K i z y ≤ 1 := forestKernel_row_le l G parent root color
  have hM : 0 ≤ 4 / (2 : ℝ) ^ n := by positivity
  induction m with
  | zero => intro j; exact Fin.elim0 j
  | succ m ih =>
    have hr : ∀ i < m, parent i = none → (root i).1 ∈ Vweld n :=
      fun i hi => hroot i (by omega)
    intro j y
    refine Fin.lastCases ?_ (fun j => ?_) j
    · rw [prefixLaw_new_marginal]
      cases hpar : parent m with
      | none =>
        have hc := FirstFreeStep.kappa_from_weld_le hG hn hl
          (hroot m (Nat.lt_succ_self m) hpar) (color m) y.1
        calc
          _ ≤ ∑ z, prefixLaw K m z * (4 / (2 : ℝ) ^ n) := by
            apply Finset.sum_le_sum
            intro z _
            apply mul_le_mul_of_nonneg_left _ (prefixLaw_nonneg K hK m z)
            simpa only [K, forestKernel, hpar] using hc
          _ = (∑ z, prefixLaw K m z) * (4 / (2 : ℝ) ^ n) :=
            (Finset.sum_mul _ _ _).symm
          _ ≤ 1 * (4 / (2 : ℝ) ^ n) := mul_le_mul_of_nonneg_right
            (prefixLaw_mass_le_one K hK hrow m) hM
          _ = _ := one_mul _
      | some a =>
        change (∑ z, prefixLaw K m z * K m z y) ≤ _
        have he (z : Fin m → Label n) : K m z y = kappa l G (color m) (z a).1 y.1 := by
          simp only [K, forestKernel, hpar]
        simp_rw [he]
        rw [marginal_pushforward (prefixLaw K m) a
          (fun v : Label n => kappa l G (color m) v.1 y.1)]
        exact KappaKernel.kappa_propagates_point_bound hG (color m)
          (marginal (prefixLaw K m) a) _ hM (fun x => ih hr a x) y.1
    · exact (prefixLaw_old_marginal_le K hK hrow m j y).trans (ih hr j y)

open Classical in
noncomputable def labelBoundary (n : ℕ) (B : Finset ℕ) : Finset (Label n) :=
  Finset.univ.filter fun x => x.1 ∈ B

lemma labelBoundary_card_le (B : Finset ℕ) : (labelBoundary n B).card ≤ B.card := by
  apply Finset.card_le_card_of_injOn Fin.val
  · intro x hx
    exact (Finset.mem_filter.mp hx).2
  · intro x hx y hy h
    exact Fin.ext h

lemma forestLaw_survival (hG : G.IsValid) (hn : 16 ≤ n) (hl : 2 ≤ l) (hln : l ≤ n - 4)
    (parent : (i : ℕ) → Option (Fin i)) (root : ℕ → Label n) (color : ℕ → Fin 3)
    (m : ℕ) (hroot : ∀ i < m, parent i = none → (root i).1 ∈ Vweld n)
    (B : Finset ℕ) (hB : Vbd n l ⊆ B) :
    1 - (m : ℝ) * (B.card : ℝ) * (4 / (2 : ℝ) ^ n) ≤
      ∑ z, prefixLaw (maskKernel (forestKernel l G parent root color) (labelBoundary n B)) m z := by
  classical
  let K := forestKernel l G parent root color
  let C := labelBoundary n B
  have hK : ∀ i z y, 0 ≤ K i z y := forestKernel_nonneg l G parent root color
  have hsafe : ∀ i z y, maskKernel K C i z y ≠ 0 →
      y.1 ∈ Vmid n l ∪ Vbd n l ∧ y.1 ∉ B := by
    intro i z y hy
    have hc : y ∉ C := by intro h; exact hy (if_pos h)
    have hk : K i z y ≠ 0 := by simpa only [maskKernel, if_neg hc] using hy
    exact ⟨KappaWalk.kappa_output_region hG hk,
      fun h => hc (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)⟩
  have hrows : ∀ i < m, ∀ z, prefixLaw (maskKernel K C) i z ≠ 0 →
      (∑ y, K i z y) = 1 := by
    intro i hi z hz
    have hs := prefixLaw_support (maskKernel K C) _ hsafe i z hz
    cases hpar : parent i with
    | none =>
      simpa only [K, forestKernel, hpar] using
        KappaWalk.kappa_weld_row_sum_eq_one hG hn hl hln (hroot i hi hpar) (color i)
    | some j =>
      have hmid : (z j).1 ∈ Vmid n l :=
        (Finset.mem_union.mp (hs j).1).resolve_right (fun h => (hs j).2 (hB h))
      simpa only [K, forestKernel, hpar] using
        KappaWalk.kappa_mid_row_sum_eq_one hG hn hl hln hmid (color i)
  have hcaps : ∀ i < m, ∀ y,
      marginal (prefixLaw K (i + 1)) (Fin.last i) y ≤ 4 / (2 : ℝ) ^ n := by
    intro i hi y
    exact forestLaw_marginal_cap hG (by omega) (by omega) parent root color (i + 1)
      (fun j hj => hroot j (by omega)) (Fin.last i) y
  have hh := masked_mass_lower K C hK (4 / (2 : ℝ) ^ n) m hrows hcaps
  have hc : (C.card : ℝ) ≤ B.card := by exact_mod_cast (labelBoundary_card_le (n := n) B)
  have hn0 : 0 ≤ (m : ℝ) := by positivity
  have hM : 0 ≤ 4 / (2 : ℝ) ^ n := by positivity
  have hmul := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc hn0) hM
  exact (sub_le_sub_left hmul 1).trans hh

lemma forestLaw_conditioned_marginal_cap (hG : G.IsValid) (hn : 16 ≤ n)
    (hl : 2 ≤ l) (hln : l ≤ n - 4)
    (parent : (i : ℕ) → Option (Fin i)) (root : ℕ → Label n) (color : ℕ → Fin 3)
    (m : ℕ) (hroot : ∀ i < m, parent i = none → (root i).1 ∈ Vweld n)
    (B : Finset ℕ) (hB : Vbd n l ⊆ B)
    (hsmall : (m : ℝ) * (B.card : ℝ) * (4 / (2 : ℝ) ^ n) ≤ 1 / 2)
    (j : Fin m) (y : Label n) :
    marginal (prefixLaw (maskKernel (forestKernel l G parent root color) (labelBoundary n B)) m) j y /
      (∑ z, prefixLaw (maskKernel (forestKernel l G parent root color) (labelBoundary n B)) m z)
        ≤ 8 / (2 : ℝ) ^ n := by
  let K := forestKernel l G parent root color
  let C := labelBoundary n B
  have hs := forestLaw_survival hG hn hl hln parent root color m hroot B hB
  have hz : (1 / 2 : ℝ) ≤ ∑ z, prefixLaw (maskKernel K C) m z := by linarith
  have hzpos : 0 < ∑ z, prefixLaw (maskKernel K C) m z := by linarith
  have hle := marginal_mono _ _
    (masked_prefixLaw_le K C (forestKernel_nonneg l G parent root color) m) j y
  have hcap := forestLaw_marginal_cap (l := l) hG (by omega) (by omega)
    parent root color m hroot j y
  apply (div_le_iff₀ hzpos).mpr
  have hM : 0 ≤ 4 / (2 : ℝ) ^ n := by positivity
  have hh := mul_le_mul_of_nonneg_left hz (by positivity : 0 ≤ 2 * (4 / (2 : ℝ) ^ n))
  calc
    _ ≤ 4 / (2 : ℝ) ^ n := hle.trans hcap
    _ ≤ _ := by convert hh using 1 <;> first | rfl | ring

end WeldedPath.Supplement.KappaForest

end

-- Solutions.WeightedForestProcess
section

namespace FiniteWeightedForest

open scoped BigOperators
open Classical

variable {V X : Type*} [DecidableEq V]

/-- Under coordinate fixing on `F`, the weights of all edges entirely in `F`
are a common constant. The other edges are exactly the sampling steps. -/
theorem edgeWeight_fixed_split (E : Finset (V × V)) (F : Finset V)
    (K : (V × V) → X → X → ℝ) (φ φ₀ : V → X)
    (hφ : ∀ v ∈ F, φ v = φ₀ v) :
    edgeWeight E K φ =
      edgeWeight (E.filter (fun p => p.1 ∈ F ∧ p.2 ∈ F)) K φ₀ *
      edgeWeight (E.filter (fun p => ¬(p.1 ∈ F ∧ p.2 ∈ F))) K φ := by
  have hfixed :
      edgeWeight (E.filter (fun p => p.1 ∈ F ∧ p.2 ∈ F)) K φ =
      edgeWeight (E.filter (fun p => p.1 ∈ F ∧ p.2 ∈ F)) K φ₀ := by
    apply Finset.prod_congr rfl
    intro p hp
    have hf := (Finset.mem_filter.mp hp).2
    exact congrArg₂ (K p) (hφ p.1 hf.1) (hφ p.2 hf.2)
  rw [← hfixed]
  exact (Finset.prod_filter_mul_prod_filter_not E (fun p => p.1 ∈ F ∧ p.2 ∈ F)
    (fun p => K p (φ p.1) (φ p.2))).symm

/-- Enumerating the edges and orienting each one away from its parent turns
the undirected edge product into the product of parent-to-child kernels. -/
theorem edgeWeight_eq_oriented_prod {m : ℕ} (E : Finset (V × V))
    (K : (V × V) → X → X → ℝ)
    (hK : ∀ p ∈ E, ∀ x y, K p x y = K p y x)
    (edges : Fin m ≃ {p // p ∈ E}) (parent child : Fin m → V)
    (horient : ∀ i, (edges i).val = (parent i, child i) ∨
      (edges i).val = (child i, parent i)) (φ : V → X) :
    edgeWeight E K φ = ∏ i : Fin m, K (edges i).val (φ (parent i)) (φ (child i)) := by
  calc
    _ = ∏ p : {p // p ∈ E}, K p.val (φ p.val.1) (φ p.val.2) :=
      (Finset.prod_coe_sort E _).symm
    _ = ∏ i : Fin m, K (edges i).val (φ (edges i).val.1) (φ (edges i).val.2) :=
      (Equiv.prod_comp edges _).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      rcases horient i with hi | hi
      · simp only [hi]
      · simpa only [hi] using hK (edges i).val (edges i).property (φ (child i)) (φ (parent i))

/-- Exact product-to-process adapter. The hypothesis identifies each local
sampling step; graph construction and the finite change of coordinates can
be proved separately without another probabilistic assumption. -/
theorem edgeWeight_eq_prefixLaw [Fintype X] {m : ℕ} (E : Finset (V × V))
    (K : (V × V) → X → X → ℝ)
    (hK : ∀ p ∈ E, ∀ x y, K p x y = K p y x)
    (edges : Fin m ≃ {p // p ∈ E}) (parent child : Fin m → V)
    (horient : ∀ i, (edges i).val = (parent i, child i) ∨
      (edges i).val = (child i, parent i))
    (step : (i : ℕ) → (Fin i → X) → X → ℝ) (φ : V → X)
    (hstep : ∀ i : Fin m,
      step i.val (WeldedPath.Supplement.KappaForest.before (fun j => φ (child j)) i)
        (φ (child i)) = K (edges i).val (φ (parent i)) (φ (child i))) :
    edgeWeight E K φ =
      WeldedPath.Supplement.KappaForest.prefixLaw step m (fun i => φ (child i)) := by
  rw [edgeWeight_eq_oriented_prod E K hK edges parent child horient φ,
    WeldedPath.Supplement.KappaForest.prefixLaw_eq_prod]
  apply Finset.prod_congr rfl
  intro i _
  exact (hstep i).symm

end FiniteWeightedForest

end

-- Solutions.WeightedFixedAssignments
section

namespace FiniteWeightedForest

open scoped BigOperators
open Classical

variable {V X : Type*} [Fintype V] [DecidableEq V] [Fintype X]

def glueFixed (F : Finset V) (φ₀ : V → X) (z : {v // v ∉ F} → X) (v : V) : X :=
  if h : v ∈ F then φ₀ v else z ⟨v, h⟩

@[simp] theorem glueFixed_on (F : Finset V) (φ₀ : V → X) (z : {v // v ∉ F} → X)
    (v : V) (hv : v ∈ F) : glueFixed F φ₀ z v = φ₀ v := by
  simp [glueFixed, hv]

@[simp] theorem glueFixed_off (F : Finset V) (φ₀ : V → X) (z : {v // v ∉ F} → X)
    (v : {v // v ∉ F}) : glueFixed F φ₀ z v = z v := by
  simp [glueFixed, v.property]

/-- Coordinate fixing leaves precisely one independent coordinate for every
vertex outside the fixed set. -/
def fixedAssignmentEquiv (F : Finset V) (φ₀ : V → X) :
    {φ : V → X // ∀ v ∈ F, φ v = φ₀ v} ≃ ({v // v ∉ F} → X) where
  toFun φ v := φ.val v
  invFun z := ⟨glueFixed F φ₀ z, fun v hv => glueFixed_on F φ₀ z v hv⟩
  left_inv φ := by
    apply Subtype.ext
    funext v
    by_cases hv : v ∈ F
    · simp [glueFixed, hv, φ.property v hv]
    · simp [glueFixed, hv]
  right_inv z := by
    funext v
    exact glueFixed_off F φ₀ z v

/-- Exact finite change of variables on a coordinate-fixing event. -/
theorem sum_fixed_assignments {R : Type*} [AddCommMonoid R]
    (F : Finset V) (φ₀ : V → X) (w : (V → X) → R) :
    (∑ φ : V → X, if ∀ v ∈ F, φ v = φ₀ v then w φ else 0) =
      ∑ z : {v // v ∉ F} → X, w (glueFixed F φ₀ z) := by
  rw [← Finset.sum_filter]
  rw [Finset.sum_subtype (p := fun φ : V → X => ∀ v ∈ F, φ v = φ₀ v)
    (Finset.univ.filter (fun φ : V → X => ∀ v ∈ F, φ v = φ₀ v))
    (fun φ => by simp) w]
  exact Fintype.sum_equiv (fixedAssignmentEquiv F φ₀) _ _ (fun φ => by
    congr 1
    exact congrArg Subtype.val ((fixedAssignmentEquiv F φ₀).left_inv φ).symm)

theorem sum_fixed_restrictions {R : Type*} [AddCommMonoid R]
    (F : Finset V) (φ₀ : V → X) (w : ({v // v ∉ F} → X) → R) :
    (∑ φ : V → X, if ∀ v ∈ F, φ v = φ₀ v then w (fun v => φ v) else 0) =
      ∑ z : {v // v ∉ F} → X, w z := by
  rw [sum_fixed_assignments F φ₀ (fun φ => w (fun v => φ v))]
  apply Finset.sum_congr rfl
  intro z _
  congr 1
  funext v
  exact glueFixed_off F φ₀ z v

/-- If a full-assignment law is a common factor times a free-coordinate
law, its normalizer has exactly the same common factor. -/
theorem sum_of_fixed_weight (F : Finset V) (φ₀ : V → X) (w : (V → X) → ℝ)
    (v : ({u // u ∉ F} → X) → ℝ) (c : ℝ)
    (hw : ∀ φ, w φ = if ∀ u ∈ F, φ u = φ₀ u then c * v (fun u => φ u) else 0) :
    (∑ φ, w φ) = c * ∑ z, v z := by
  simp_rw [hw]
  rw [sum_fixed_restrictions F φ₀ (fun z => c * v z), Finset.mul_sum]

/-- The corresponding normalized laws agree pointwise, including assignments
outside the fixed-coordinate event and zero free normalizers. -/
theorem normalize_fixed_weight (F : Finset V) (φ₀ : V → X) (w : (V → X) → ℝ)
    (v : ({u // u ∉ F} → X) → ℝ) (c : ℝ) (hc : c ≠ 0)
    (hw : ∀ φ, w φ = if ∀ u ∈ F, φ u = φ₀ u then c * v (fun u => φ u) else 0)
    (φ : V → X) :
    w φ / (∑ ψ, w ψ) =
      if ∀ u ∈ F, φ u = φ₀ u then v (fun u => φ u) / (∑ z, v z) else 0 := by
  rw [sum_of_fixed_weight F φ₀ w v c hw, hw φ]
  split_ifs
  · exact mul_div_mul_left _ _ hc
  · exact zero_div _

/-- Marginal probabilities of a free vertex transfer without an additional
cardinality factor. -/
theorem fixed_weight_marginal (F : Finset V) (φ₀ : V → X) (w : (V → X) → ℝ)
    (v : ({u // u ∉ F} → X) → ℝ) (c : ℝ) (hc : c ≠ 0)
    (hw : ∀ φ, w φ = if ∀ u ∈ F, φ u = φ₀ u then c * v (fun u => φ u) else 0)
    (u : {u // u ∉ F}) (x : X) :
    (∑ φ, if φ u = x then w φ else 0) / (∑ φ, w φ) =
      (∑ z, if z u = x then v z else 0) / (∑ z, v z) := by
  have hevent (φ : V → X) :
      (if φ u = x then w φ else 0) =
        if ∀ a ∈ F, φ a = φ₀ a then
          c * (if (fun a : {a // a ∉ F} => φ a) u = x then v (fun a => φ a) else 0) else 0 := by
    rw [hw φ]
    split_ifs <;> simp_all
  have hnum := sum_of_fixed_weight F φ₀ (fun φ => if φ u = x then w φ else 0)
    (fun z => if z u = x then v z else 0) c hevent
  rw [hnum, sum_of_fixed_weight F φ₀ w v c hw]
  exact mul_div_mul_left _ _ hc

end FiniteWeightedForest

end

-- Solutions.WeldedPathComponentProcess
section

namespace WeldedPath.Supplement.ComponentProcess

open scoped BigOperators
open Classical FiniteWeightedForest ForestOrder ForestFactorization KappaForest

variable {n : ℕ} (H : AbsForest n) (φ₀ : Fin H.k → Label n) (s : Fin H.k)

noncomputable abbrev stages := Fintype.card ↥(freeVertices H φ₀ s)

variable (C : ParentOrder H φ₀ s)

noncomputable def processParent (i : ℕ) : Option (Fin i) :=
  if hi : i < stages H φ₀ s then C.parent ⟨i, hi⟩ else none

noncomputable def processRoot (i : ℕ) : Label n :=
  if hi : i < stages H φ₀ s then φ₀ (C.fixed ⟨i, hi⟩) else 0

noncomputable def processColor (i : ℕ) : Fin 3 :=
  if hi : i < stages H φ₀ s then H.color (C.edge ⟨i, hi⟩).val else 0

noncomputable def processKernel (l : ℕ) (G : WeldedInstance n) :=
  forestKernel l G (processParent H φ₀ s C) (processRoot H φ₀ s C)
    (processColor H φ₀ s C)

lemma process_root_weld (i : ℕ) (hi : i < stages H φ₀ s)
    (hp : processParent H φ₀ s C i = none) :
    (processRoot H φ₀ s C i).val ∈ Vweld n := by
  simp only [processParent, dif_pos hi] at hp
  simpa only [processRoot, dif_pos hi] using C.fixed_weld ⟨i, hi⟩ hp

lemma free_edge_weight_eq_process (l : ℕ) (G : WeldedInstance n) (hG : G.IsValid)
    (φ : Fin H.k → Label n) (hφ : ∀ u ∈ H.Sfix φ₀ s, φ u = φ₀ u) :
    edgeWeight (freeEdges H φ₀ s) (componentKernel l G H) φ =
      prefixLaw (processKernel H φ₀ s C l G) (stages H φ₀ s)
        (fun i => φ (C.order i).val) := by
  apply edgeWeight_eq_prefixLaw (freeEdges H φ₀ s) (componentKernel l G H)
    (fun _ _ x y => KappaKernel.kappa_symm hG _ _ _)
    C.edge (parentVertex H (fun i => (C.order i).val) C.fixed C.parent)
    (fun i => (C.order i).val) (fun i => (C.edge_endpoints i).symm)
  intro i
  unfold processKernel forestKernel processParent processRoot processColor
  simp only [dif_pos i.isLt, componentKernel]
  cases hp : C.parent i with
  | none =>
    simp only [hp, parentVertex, hφ _ (C.fixed_mem i hp)]
  | some j =>
    simp only [hp, parentVertex, before]

noncomputable def fixedEdges : Finset (Fin H.k × Fin H.k) :=
  (componentEdges H s).filter (fun e => e.1 ∈ H.Sfix φ₀ s ∧ e.2 ∈ H.Sfix φ₀ s)

lemma component_nonfixed_edges :
    (componentEdges H s).filter (fun e => ¬(e.1 ∈ H.Sfix φ₀ s ∧ e.2 ∈ H.Sfix φ₀ s)) =
      freeEdges H φ₀ s := by
  ext e
  simp only [componentEdges, freeEdges, Finset.mem_filter, and_assoc]

lemma component_edge_weight_split (l : ℕ) (G : WeldedInstance n) (hG : G.IsValid)
    (φ : Fin H.k → Label n) (hφ : ∀ u ∈ H.Sfix φ₀ s, φ u = φ₀ u) :
    edgeWeight (componentEdges H s) (componentKernel l G H) φ =
      edgeWeight (fixedEdges H φ₀ s) (componentKernel l G H) φ₀ *
        prefixLaw (processKernel H φ₀ s C l G) (stages H φ₀ s)
          (fun i => φ (C.order i).val) := by
  rw [edgeWeight_fixed_split _ (H.Sfix φ₀ s) _ _ φ₀ hφ,
    component_nonfixed_edges H φ₀ s,
    free_edge_weight_eq_process H φ₀ s C l G hG φ hφ]
  rfl

lemma reference_region (l : ℕ) (G : WeldedInstance n)
    (hsize : (H.comp s).card ≠ 1) (hμ : H.muComp l G s φ₀ ≠ 0) :
    ∀ u ∈ H.comp s, (φ₀ u).val ∈ Vmid n l ∪ Vbd n l := by
  intro u hu
  rw [muComp_eq_scale_forestWeight l G H s hsize φ₀] at hμ
  have hw := (mul_ne_zero_iff.mp hμ).2
  unfold forestWeight at hw
  split_ifs at hw with ha
  · exact ha u hu
  · exact (hw rfl).elim

lemma process_support (l : ℕ) (G : WeldedInstance n) (hG : G.IsValid)
    (z : Fin (stages H φ₀ s) → Label n)
    (hz : prefixLaw (processKernel H φ₀ s C l G) (stages H φ₀ s) z ≠ 0) :
    ∀ i, (z i).val ∈ Vmid n l ∪ Vbd n l := by
  exact prefixLaw_support (processKernel H φ₀ s C l G)
    (fun y : Label n => y.val ∈ Vmid n l ∪ Vbd n l)
    (fun _ _ _ hy => KappaWalk.kappa_output_region hG hy) _ z hz

noncomputable def processScale (l : ℕ) (G : WeldedInstance n) : ℝ :=
  componentScale l G H s * edgeWeight (fixedEdges H φ₀ s) (componentKernel l G H) φ₀

lemma muComp_eq_process_on_fixed (l : ℕ) (G : WeldedInstance n) (hG : G.IsValid)
    (hsize : (H.comp s).card ≠ 1) (hμ : H.muComp l G s φ₀ ≠ 0)
    (φ : Fin H.k → Label n) (hφ : ∀ u ∈ H.Sfix φ₀ s, φ u = φ₀ u) :
    H.muComp l G s φ = processScale H φ₀ s l G *
      prefixLaw (processKernel H φ₀ s C l G) (stages H φ₀ s)
        (fun i => φ (C.order i).val) := by
  rw [muComp_eq_scale_forestWeight l G H s hsize φ]
  have he := component_edge_weight_split H φ₀ s C l G hG φ hφ
  unfold forestWeight
  split_ifs with ha
  · rw [he]
    exact (mul_assoc _ _ _).symm
  · have hz : prefixLaw (processKernel H φ₀ s C l G) (stages H φ₀ s)
        (fun i => φ (C.order i).val) = 0 := by
      by_contra hnz
      apply ha
      intro u hu
      by_cases hf : u ∈ H.Sfix φ₀ s
      · rw [hφ u hf]
        exact reference_region H φ₀ s l G hsize hμ u hu
      · let v : freeVertices H φ₀ s := ⟨u, Finset.mem_sdiff.mpr ⟨hu, hf⟩⟩
        have h := process_support H φ₀ s C l G hG _ hnz (C.order.symm v)
        simpa only [Equiv.apply_symm_apply] using h
    simp only [hz, mul_zero]

include C in
lemma processScale_ne_zero (l : ℕ) (G : WeldedInstance n) (hG : G.IsValid)
    (hsize : (H.comp s).card ≠ 1) (hμ : H.muComp l G s φ₀ ≠ 0) :
    processScale H φ₀ s l G ≠ 0 := by
  rw [muComp_eq_process_on_fixed H φ₀ s C l G hG hsize hμ φ₀ (fun _ _ => rfl)] at hμ
  exact (mul_ne_zero_iff.mp hμ).1

noncomputable def freeComplementEquiv (hconn : H.comp s = Finset.univ) :
    freeVertices H φ₀ s ≃ {u : Fin H.k // u ∉ H.Sfix φ₀ s} where
  toFun v := ⟨v.val, (free_vertex_spec H φ₀ s v).2⟩
  invFun v := ⟨v.val, Finset.mem_sdiff.mpr ⟨by rw [hconn]; exact Finset.mem_univ _, v.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def coordinateEquiv (hconn : H.comp s = Finset.univ) :
    ({u : Fin H.k // u ∉ H.Sfix φ₀ s} → Label n) ≃ (Fin (stages H φ₀ s) → Label n) :=
  Equiv.arrowCongr (C.order.trans (freeComplementEquiv H φ₀ s hconn)).symm (Equiv.refl _)

lemma sum_fixed_coordinates (hconn : H.comp s = Finset.univ)
    (f : (Fin (stages H φ₀ s) → Label n) → ℝ) :
    (∑ φ : Fin H.k → Label n, if ∀ u ∈ H.Sfix φ₀ s, φ u = φ₀ u then
      f (fun i => φ (C.order i).val) else 0) = ∑ z, f z := by
  have hh := sum_fixed_restrictions (H.Sfix φ₀ s) φ₀
    (fun z => f (coordinateEquiv H φ₀ s C hconn z))
  calc
    _ = ∑ z, f (coordinateEquiv H φ₀ s C hconn z) := by
      convert hh using 1
      apply Finset.sum_congr rfl
      intro φ _
      split_ifs <;> rfl
    _ = _ := Equiv.sum_comp (coordinateEquiv H φ₀ s C hconn) f

lemma free_avoid_iff_order (hconn : H.comp s = Finset.univ)
    (B : Finset ℕ) (φ : Fin H.k → Label n) :
    (∀ u, u ∉ H.Sfix φ₀ s → (φ u).val ∉ B) ↔
      ∀ i, (φ (C.order i).val).val ∉ B := by
  constructor
  · intro h i
    exact h _ (free_vertex_spec H φ₀ s (C.order i)).2
  · intro h u hu
    let v : freeVertices H φ₀ s :=
      ⟨u, Finset.mem_sdiff.mpr ⟨by rw [hconn]; exact Finset.mem_univ _, hu⟩⟩
    have hh := h (C.order.symm v)
    simpa only [Equiv.apply_symm_apply] using hh

noncomputable def fixedAvoidWeight (l : ℕ) (G : WeldedInstance n) (B : Finset ℕ)
    (φ : Fin H.k → Label n) : ℝ :=
  if (∀ u ∈ H.Sfix φ₀ s, φ u = φ₀ u) ∧
    (∀ u, u ∉ H.Sfix φ₀ s → (φ u).val ∉ B) then H.muComp l G s φ else 0

noncomputable def maskedLaw (l : ℕ) (G : WeldedInstance n) (B : Finset ℕ) :=
  prefixLaw (maskKernel (processKernel H φ₀ s C l G) (labelBoundary n B))
    (stages H φ₀ s)

lemma fixedAvoidWeight_eq_process (l : ℕ) (G : WeldedInstance n) (hG : G.IsValid)
    (hconn : H.comp s = Finset.univ) (hsize : (H.comp s).card ≠ 1)
    (hμ : H.muComp l G s φ₀ ≠ 0) (B : Finset ℕ) (φ : Fin H.k → Label n) :
    fixedAvoidWeight H φ₀ s l G B φ =
      if ∀ u ∈ H.Sfix φ₀ s, φ u = φ₀ u then processScale H φ₀ s l G *
        maskedLaw H φ₀ s C l G B (fun i => φ (C.order i).val) else 0 := by
  have hm : maskedLaw H φ₀ s C l G B (fun i => φ (C.order i).val) =
      if ∀ u, u ∉ H.Sfix φ₀ s → (φ u).val ∉ B then
        prefixLaw (processKernel H φ₀ s C l G) (stages H φ₀ s)
          (fun i => φ (C.order i).val) else 0 := by
    unfold maskedLaw
    rw [masked_prefixLaw_eq]
    simp only [labelBoundary, Finset.mem_filter, Finset.mem_univ, true_and,
      free_avoid_iff_order H φ₀ s C hconn B φ]
  by_cases ha : ∀ u ∈ H.Sfix φ₀ s, φ u = φ₀ u
  · rw [if_pos ha, hm]
    unfold fixedAvoidWeight
    by_cases hb : ∀ u, u ∉ H.Sfix φ₀ s → (φ u).val ∉ B
    · rw [if_pos ⟨ha, hb⟩, if_pos hb]
      exact muComp_eq_process_on_fixed H φ₀ s C l G hG hsize hμ φ ha
    · simp only [ha, hb, and_false, if_false, mul_zero]
  · simp only [fixedAvoidWeight, ha, false_and, if_false]

lemma conditional_event_eq_process (l : ℕ) (G : WeldedInstance n) (hG : G.IsValid)
    (hconn : H.comp s = Finset.univ) (hsize : (H.comp s).card ≠ 1)
    (hμ : H.muComp l G s φ₀ ≠ 0) (B : Finset ℕ)
    (event : (Fin (stages H φ₀ s) → Label n) → Prop) :
    (∑ φ : Fin H.k → Label n, if event (fun i => φ (C.order i).val) then
      fixedAvoidWeight H φ₀ s l G B φ else 0) /
      (∑ φ, fixedAvoidWeight H φ₀ s l G B φ) =
    (∑ z, if event z then maskedLaw H φ₀ s C l G B z else 0) /
      (∑ z, maskedLaw H φ₀ s C l G B z) := by
  classical
  let c := processScale H φ₀ s l G
  let L := maskedLaw H φ₀ s C l G B
  have hc : c ≠ 0 := processScale_ne_zero H φ₀ s C l G hG hsize hμ
  have hden : (∑ φ, fixedAvoidWeight H φ₀ s l G B φ) = c * ∑ z, L z := by
    simp_rw [fixedAvoidWeight_eq_process H φ₀ s C l G hG hconn hsize hμ B]
    rw [sum_fixed_coordinates H φ₀ s C hconn (fun z => c * L z), Finset.mul_sum]
  have he (φ : Fin H.k → Label n) :
      (if event (fun i => φ (C.order i).val) then fixedAvoidWeight H φ₀ s l G B φ else 0) =
      if ∀ u ∈ H.Sfix φ₀ s, φ u = φ₀ u then
        c * (if event (fun i => φ (C.order i).val) then L (fun i => φ (C.order i).val) else 0)
      else 0 := by
    rw [fixedAvoidWeight_eq_process H φ₀ s C l G hG hconn hsize hμ B φ]
    split_ifs <;> simp_all [c, L]
  simp_rw [he]
  rw [sum_fixed_coordinates H φ₀ s C hconn
    (fun z => c * (if event z then L z else 0)), ← Finset.mul_sum, hden]
  exact mul_div_mul_left _ _ hc

end WeldedPath.Supplement.ComponentProcess

end

-- Solutions.WeldedPathReciprocalClasses
section

namespace WeldedPath.Supplement.ReciprocalClasses

open scoped BigOperators
open Classical KappaKernel

variable {n l : ℕ} (G : WeldedInstance n)

/-- The reciprocal class size at the first edge, zero for an undefined transition. -/
noncomputable def firstEdgeCap (α : Fin 3) (u : ℕ) : ℝ :=
  match permData l G u α with
  | none => 0
  | some ⟨b, _, _⟩ => 1 / (classSize l G b : ℝ)

theorem firstEdgeCap_nonneg (α : Fin 3) (u : ℕ) : 0 ≤ firstEdgeCap (l := l) G α u := by
  unfold firstEdgeCap
  split <;> positivity

theorem kappa_le_firstEdgeCap (α : Fin 3) (u v : ℕ) :
    kappa l G α u v ≤ firstEdgeCap (l := l) G α u := by
  cases hpd : permData l G u α with
  | none => simp [kappa, firstEdgeCap, hpd]
  | some d =>
    obtain ⟨b, e, t⟩ := d
    simpa only [firstEdgeCap, hpd] using kappa_le_inv_classSize hpd v

noncomputable def endpointCap (b : PClass n l) (u : ℕ) : ℝ :=
  if u ∈ (G.classEdges l b.1).image Edge.tail ∨
      u ∈ (G.classEdges l b.1).image (Edge.head n) then
    1 / (classSize l G b : ℝ) else 0

theorem firstEdgeCap_le_endpoint_sum (α : Fin 3) (u : ℕ) :
    firstEdgeCap (l := l) G α u ≤ ∑ b : PClass n l, endpointCap G b u := by
  cases hpd : permData l G u α with
  | none =>
    simp only [firstEdgeCap, hpd]
    apply Finset.sum_nonneg
    intro b _
    unfold endpointCap
    split_ifs <;> positivity
  | some d =>
    obtain ⟨b, e, t⟩ := d
    have hi := (eAlpha_spec (permData_eAlpha hpd)).2.2
    have hm : u ∈ (G.classEdges l b.1).image Edge.tail ∨
        u ∈ (G.classEdges l b.1).image (Edge.head n) := by
      rcases hi with hi | hi
      · exact Or.inl (Finset.mem_image.mpr ⟨e.1, e.2, hi.symm⟩)
      · exact Or.inr (Finset.mem_image.mpr ⟨e.1, e.2, hi.symm⟩)
    have he : firstEdgeCap (l := l) G α u = endpointCap G b u := by
      simp only [firstEdgeCap, hpd, endpointCap, if_pos hm]
    rw [he]
    apply Finset.single_le_sum _ (Finset.mem_univ b)
    intro c _
    unfold endpointCap
    split_ifs <;> positivity

theorem endpointCap_sum_le_two (b : PClass n l) :
    (∑ u : Label n, endpointCap G b u.1) ≤ 2 := by
  have htail := sum_uniform_finset_le_one (X := Label n) Fin.val Fin.val_injective
    ((G.classEdges l b.1).image Edge.tail) (classSize l G b) Finset.card_image_le
  have hhead := sum_uniform_finset_le_one (X := Label n) Fin.val Fin.val_injective
    ((G.classEdges l b.1).image (Edge.head n)) (classSize l G b) Finset.card_image_le
  calc
    _ ≤ ∑ u : Label n,
        ((if u.1 ∈ (G.classEdges l b.1).image Edge.tail then
          1 / (classSize l G b : ℝ) else 0) +
        (if u.1 ∈ (G.classEdges l b.1).image (Edge.head n) then
          1 / (classSize l G b : ℝ) else 0)) := by
      apply Finset.sum_le_sum
      intro u _
      unfold endpointCap
      split_ifs <;> simp_all <;> positivity
    _ ≤ 2 := by rw [Finset.sum_add_distrib]; linarith

theorem class_count_le (hln : l ≤ n) : (BEdge n l).card ≤ 6 * (n + 1) := by
  unfold BEdge
  have h₁ := Finset.card_image_le (s :=
    (Finset.Icc (n - l) (n + l)) ×ˢ (Finset.univ : Finset (Fin 3)))
    (f := fun p => EdgeClass.tr p.1 p.2)
  have h₂ := Finset.card_image_le (s := (Finset.univ : Finset (Fin 3)))
    (f := EdgeClass.wld)
  have h₃ := Finset.card_union_le
    (((Finset.Icc (n - l) (n + l)) ×ˢ (Finset.univ : Finset (Fin 3))).image
      (fun p => EdgeClass.tr p.1 p.2))
    ((Finset.univ : Finset (Fin 3)).image EdgeClass.wld)
  simp only [Finset.card_product, Nat.card_Icc, Finset.card_univ, Fintype.card_fin] at h₁ h₂
  omega

/-- Summing reciprocal class sizes costs only the number of columns: each
class is charged at most once by its tails and once by its heads. -/
theorem firstEdgeCap_sum_le (hln : l ≤ n) (α : Fin 3) :
    (∑ u : Label n, firstEdgeCap (l := l) G α u.1) ≤ 12 * ((n : ℝ) + 1) := by
  calc
    _ ≤ ∑ u : Label n, ∑ b : PClass n l, endpointCap G b u.1 :=
      Finset.sum_le_sum fun u _ => firstEdgeCap_le_endpoint_sum G α u.1
    _ = ∑ b : PClass n l, ∑ u : Label n, endpointCap G b u.1 := Finset.sum_comm
    _ ≤ ∑ b : PClass n l, (2 : ℝ) :=
      Finset.sum_le_sum fun b _ => endpointCap_sum_le_two G b
    _ = (Fintype.card (PClass n l) : ℝ) * 2 := by simp
    _ ≤ (6 * ((n : ℝ) + 1)) * 2 := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have h := class_count_le hln
      simpa only [PClass, Fintype.card_coe, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat,
        Nat.cast_one] using (Nat.cast_le.mpr h : ((BEdge n l).card : ℝ) ≤ (6 * (n + 1) : ℕ))
    _ = _ := by ring

/-- This is the class-counting part of the lowest-common-ancestor collision
estimate: a parent with point mass at most M pays only O(n) M in total. -/
theorem expected_firstEdgeCap_le (hln : l ≤ n) (α : Fin 3)
    (p : Label n → ℝ) (M : ℝ) (hM : 0 ≤ M) (hp : ∀ u, p u ≤ M) :
    (∑ u, p u * firstEdgeCap (l := l) G α u.1) ≤ 12 * ((n : ℝ) + 1) * M := by
  calc
    _ ≤ ∑ u, M * firstEdgeCap (l := l) G α u.1 := Finset.sum_le_sum
      fun u _ => mul_le_mul_of_nonneg_right (hp u) (firstEdgeCap_nonneg G α u.1)
    _ = M * ∑ u : Label n, firstEdgeCap (l := l) G α u.1 := (Finset.mul_sum _ _ _).symm
    _ ≤ M * (12 * ((n : ℝ) + 1)) := mul_le_mul_of_nonneg_left (firstEdgeCap_sum_le G hln α) hM
    _ = _ := by ring

end WeldedPath.Supplement.ReciprocalClasses

end

-- Solutions.WeldedPathBranchCollision
section

namespace WeldedPath.Supplement.BranchCollision

open scoped BigOperators
open Classical KappaKernel KappaWalk ReciprocalClasses

variable {n l : ℕ} {G : WeldedInstance n}

noncomputable def pointMass (u : Label n) : Label n → ℝ := fun y => if y = u then 1 else 0

theorem pointMass_nonneg (u y : Label n) : 0 ≤ pointMass u y := by
  unfold pointMass
  split_ifs <;> positivity

theorem pointMass_sum (u : Label n) : (∑ y, pointMass u y) = 1 := by
  simp [pointMass]

theorem step_pointMass (α : Fin 3) (u y : Label n) :
    step l G α (pointMass u) y = kappa l G α u.1 y.1 := by
  simp [step, pointMass]

/-- The walk is linear in its initial law, written in the point-mass basis. -/
theorem walk_matrix (cs : List (Fin 3)) (p : Label n → ℝ) (y : Label n) :
    walk l G cs p y = ∑ u, p u * walk l G cs (pointMass u) y := by
  induction cs generalizing p with
  | nil => simp [walk, pointMass]
  | cons α cs ih =>
    have hc (u : Label n) : walk l G (α :: cs) (pointMass u) y =
        ∑ x, kappa l G α u.1 x.1 * walk l G cs (pointMass x) y := by
      rw [walk, ih]
      simp_rw [step_pointMass]
    rw [walk, ih]
    simp only [step, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u _
    rw [hc, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring

theorem walk_cons_matrix (α : Fin 3) (cs : List (Fin 3)) (u y : Label n) :
    walk l G (α :: cs) (pointMass u) y =
      ∑ x, kappa l G α u.1 x.1 * walk l G cs (pointMass x) y := by
  rw [walk, walk_matrix]
  simp_rw [step_pointMass]

noncomputable def meet (cs ds : List (Fin 3)) (u v : Label n) : ℝ :=
  ∑ y, walk l G cs (pointMass u) y * walk l G ds (pointMass v) y

theorem meet_nonneg (cs ds : List (Fin 3)) (u v : Label n) :
    0 ≤ meet (l := l) (G := G) cs ds u v := by
  apply Finset.sum_nonneg
  intro y _
  exact mul_nonneg (walk_nonneg l G cs _ (pointMass_nonneg u) y)
    (walk_nonneg l G ds _ (pointMass_nonneg v) y)

theorem meet_symm (cs ds : List (Fin 3)) (u v : Label n) :
    meet (l := l) (G := G) cs ds u v = meet (l := l) (G := G) ds cs v u := by
  apply Finset.sum_congr rfl
  intro y _
  exact mul_comm _ _

theorem meet_cons_left (α : Fin 3) (cs ds : List (Fin 3)) (u v : Label n) :
    meet (l := l) (G := G) (α :: cs) ds u v =
      ∑ x, kappa l G α u.1 x.1 * meet (l := l) (G := G) cs ds x v := by
  unfold meet
  simp_rw [walk_cons_matrix, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

theorem meet_cons_right (α : Fin 3) (cs ds : List (Fin 3)) (u v : Label n) :
    meet (l := l) (G := G) cs (α :: ds) u v =
      ∑ x, kappa l G α v.1 x.1 * meet (l := l) (G := G) cs ds u x := by
  rw [meet_symm, meet_cons_left]
  apply Finset.sum_congr rfl
  intro x _
  rw [meet_symm ds cs x u]

theorem meet_nil_nil (u v : Label n) :
    meet (l := l) (G := G) [] [] u v = if u = v then 1 else 0 := by
  simp [meet, walk, pointMass, eq_comm]

theorem meet_from_weld_le (hG : G.IsValid) (hn : 2 ≤ n) (hl : 1 ≤ l)
    (α : Fin 3) (cs ds : List (Fin 3)) (u v : Label n) (hu : u.1 ∈ Vweld n) :
    meet (l := l) (G := G) (α :: cs) ds u v ≤ 4 / (2 : ℝ) ^ n := by
  have hM : 0 ≤ 4 / (2 : ℝ) ^ n := by positivity
  have hc : ∀ y, walk l G (α :: cs) (pointMass u) y ≤ 4 / (2 : ℝ) ^ n := by
    apply walk_point_bound hG cs (step l G α (pointMass u)) _ hM
    intro y
    rw [step_pointMass]
    exact FirstFreeStep.kappa_from_weld_le hG hn hl hu α y.1
  calc
    _ ≤ ∑ y, (4 / (2 : ℝ) ^ n) * walk l G ds (pointMass v) y := by
      apply Finset.sum_le_sum
      intro y _
      exact mul_le_mul_of_nonneg_right (hc y) (walk_nonneg l G ds _ (pointMass_nonneg v) y)
    _ = (4 / (2 : ℝ) ^ n) * ∑ y, walk l G ds (pointMass v) y := (Finset.mul_sum _ _ _).symm
    _ ≤ (4 / (2 : ℝ) ^ n) * 1 := by
      apply mul_le_mul_of_nonneg_left _ hM
      simpa only [pointMass_sum] using walk_mass_le l G ds _ (pointMass_nonneg v)
    _ = _ := mul_one _

/-- After the first edge, every further symmetric substochastic transition
preserves the reciprocal-class point bound. -/
theorem walk_firstEdgeCap (hG : G.IsValid) (α : Fin 3) (cs : List (Fin 3))
    (u y : Label n) :
    walk l G (α :: cs) (pointMass u) y ≤ firstEdgeCap (l := l) G α u.1 := by
  apply walk_point_bound hG cs (step l G α (pointMass u)) _
    (firstEdgeCap_nonneg G α u.1) _ y
  intro z
  rw [step_pointMass]
  exact kappa_le_firstEdgeCap G α u.1 z.1

/-- The coincidence mass of two independent branches from one parent is
bounded by the reciprocal class size of either nonempty branch's first edge. -/
theorem two_branch_collision_le (hG : G.IsValid) (α : Fin 3)
    (cs ds : List (Fin 3)) (u : Label n) :
    (∑ y, walk l G (α :: cs) (pointMass u) y *
      walk l G ds (pointMass u) y) ≤ firstEdgeCap (l := l) G α u.1 := by
  calc
    _ ≤ ∑ y, firstEdgeCap (l := l) G α u.1 * walk l G ds (pointMass u) y := by
      apply Finset.sum_le_sum
      intro y _
      exact mul_le_mul_of_nonneg_right (walk_firstEdgeCap hG α cs u y)
        (walk_nonneg l G ds (pointMass u) (pointMass_nonneg u) y)
    _ = firstEdgeCap (l := l) G α u.1 * ∑ y, walk l G ds (pointMass u) y :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ firstEdgeCap (l := l) G α u.1 * 1 := by
      apply mul_le_mul_of_nonneg_left _ (firstEdgeCap_nonneg G α u.1)
      simpa only [pointMass_sum] using
        walk_mass_le l G ds (pointMass u) (pointMass_nonneg u)
    _ = _ := mul_one _

/-- Averaging over a free lowest common ancestor costs O(n) times its point
mass bound. Both branches may have arbitrary length; one may be empty. -/
theorem averaged_branch_collision_le (hG : G.IsValid) (hln : l ≤ n)
    (α : Fin 3) (cs ds : List (Fin 3)) (p : Label n → ℝ)
    (hp : ∀ u, 0 ≤ p u) (M : ℝ) (hM : 0 ≤ M) (hcap : ∀ u, p u ≤ M) :
    (∑ u, p u * ∑ y, walk l G (α :: cs) (pointMass u) y *
      walk l G ds (pointMass u) y) ≤ 12 * ((n : ℝ) + 1) * M := by
  calc
    _ ≤ ∑ u, p u * firstEdgeCap (l := l) G α u.1 := Finset.sum_le_sum
      fun u _ => mul_le_mul_of_nonneg_left (two_branch_collision_le hG α cs ds u) (hp u)
    _ ≤ _ := expected_firstEdgeCap_le G hln α p M hM hcap

end WeldedPath.Supplement.BranchCollision

end

-- Solutions.WeldedPathForestCollision
section

namespace WeldedPath.Supplement.ForestCollision

open KappaForest KappaKernel KappaWalk BranchCollision
open scoped BigOperators

variable {X : Type*} [Fintype X] {m : ℕ}

noncomputable def pairExpectation (w : (Fin m → X) → ℝ) (a b : Fin m)
    (F : X → X → ℝ) : ℝ := ∑ z, w z * F (z a) (z b)

lemma pairExpectation_old_le (K : (i : ℕ) → (Fin i → X) → X → ℝ)
    (hK : ∀ i z y, 0 ≤ K i z y) (hrow : ∀ i z, ∑ y, K i z y ≤ 1)
    (m : ℕ) (a b : Fin m) (F : X → X → ℝ) (hF : ∀ x y, 0 ≤ F x y) :
    pairExpectation (prefixLaw K (m + 1)) a.castSucc b.castSucc F ≤
      pairExpectation (prefixLaw K m) a b F := by
  unfold pairExpectation
  rw [sum_snoc]
  simp only [prefixLaw_snoc, Fin.snoc_castSucc]
  apply Finset.sum_le_sum
  intro z _
  calc
    _ = (prefixLaw K m z * F (z a) (z b)) * ∑ y, K m z y := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      ring
    _ ≤ (prefixLaw K m z * F (z a) (z b)) * 1 :=
      mul_le_mul_of_nonneg_left (hrow m z)
        (mul_nonneg (prefixLaw_nonneg K hK m z) (hF _ _))
    _ = _ := mul_one _

lemma pairExpectation_new (K : (i : ℕ) → (Fin i → X) → X → ℝ)
    (m : ℕ) (b : Fin m) (F : X → X → ℝ) :
    pairExpectation (prefixLaw K (m + 1)) (Fin.last m) b.castSucc F =
      ∑ z : Fin m → X, prefixLaw K m z * ∑ y, K m z y * F y (z b) := by
  unfold pairExpectation
  rw [sum_snoc]
  simp only [prefixLaw_snoc, Fin.snoc_castSucc, Fin.snoc_last]
  apply Finset.sum_congr rfl
  intro z _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

lemma pairExpectation_diagonal (w : (Fin m → X) → ℝ) (a : Fin m)
    (F : X → X → ℝ) :
    pairExpectation w a a F = ∑ x, marginal w a x * F x x :=
  marginal_pushforward w a (fun x => F x x)

lemma marginal_nonneg (w : (Fin m → X) → ℝ) (hw : ∀ z, 0 ≤ w z)
    (j : Fin m) (x : X) : 0 ≤ marginal w j x := by
  apply Finset.sum_nonneg
  intro z _
  split_ifs
  · exact hw z
  · exact le_rfl

variable {n l : ℕ} {G : WeldedInstance n}

lemma pairExpectation_meet_symm (w : (Fin m → Label n) → ℝ) (a b : Fin m)
    (cs ds : List (Fin 3)) :
    pairExpectation w a b (meet (l := l) (G := G) cs ds) =
      pairExpectation w b a (meet (l := l) (G := G) ds cs) := by
  apply Finset.sum_congr rfl
  intro z _
  rw [meet_symm cs ds]

lemma pairExpectation_new_meet (K : (i : ℕ) → (Fin i → Label n) → Label n → ℝ)
    (m : ℕ) (b : Fin m) (α : Fin 3) (u : (Fin m → Label n) → Label n)
    (hK : ∀ z y, K m z y = kappa l G α (u z).1 y.1) (cs ds : List (Fin 3)) :
    pairExpectation (prefixLaw K (m + 1)) (Fin.last m) b.castSucc
        (meet (l := l) (G := G) cs ds) =
      ∑ z : Fin m → Label n, prefixLaw K m z * meet (l := l) (G := G) (α :: cs) ds (u z) (z b) := by
  rw [pairExpectation_new]
  simp_rw [hK, ← meet_cons_left]

lemma diagonal_meet_bound (hG : G.IsValid) (hln : l ≤ n)
    (w : (Fin m → Label n) → ℝ) (hw : ∀ z, 0 ≤ w z) (a : Fin m)
    (M : ℝ) (hM : 0 ≤ M) (hcap : ∀ x, marginal w a x ≤ M)
    (cs ds : List (Fin 3)) (hne : cs ≠ [] ∨ ds ≠ []) :
    pairExpectation w a a (meet (l := l) (G := G) cs ds) ≤
      12 * ((n : ℝ) + 1) * M := by
  classical
  cases cs with
  | nil =>
    cases ds with
    | nil => simp at hne
    | cons α ds =>
      rw [pairExpectation_meet_symm, pairExpectation_diagonal]
      exact averaged_branch_collision_le hG hln α ds [] (marginal w a)
        (marginal_nonneg w hw a) M hM hcap
  | cons α cs =>
    rw [pairExpectation_diagonal]
    exact averaged_branch_collision_le hG hln α cs ds (marginal w a)
      (marginal_nonneg w hw a) M hM hcap

lemma forest_meet_bound (hG : G.IsValid) (hn : 2 ≤ n) (hl : 1 ≤ l) (hln : l ≤ n)
    (parent : (i : ℕ) → Option (Fin i)) (root : ℕ → Label n) (color : ℕ → Fin 3)
    (m : ℕ) (hroot : ∀ i < m, parent i = none → (root i).1 ∈ Vweld n) :
    ∀ (a b : Fin m) (cs ds : List (Fin 3)), a ≠ b ∨ cs ≠ [] ∨ ds ≠ [] →
      pairExpectation (prefixLaw (forestKernel l G parent root color) m) a b
          (meet (l := l) (G := G) cs ds) ≤
        12 * ((n : ℝ) + 1) * (4 / (2 : ℝ) ^ n) := by
  classical
  let K := forestKernel l G parent root color
  have hK : ∀ i z y, 0 ≤ K i z y := forestKernel_nonneg l G parent root color
  have hrow : ∀ i z, ∑ y, K i z y ≤ 1 := forestKernel_row_le l G parent root color
  have hM : 0 ≤ 4 / (2 : ℝ) ^ n := by positivity
  have hCM : 4 / (2 : ℝ) ^ n ≤ 12 * ((n : ℝ) + 1) * (4 / (2 : ℝ) ^ n) := by
    have hn0 : (0 : ℝ) ≤ n := by positivity
    nlinarith
  induction m with
  | zero => intro a; exact Fin.elim0 a
  | succ m ih =>
    have hr : ∀ i < m, parent i = none → (root i).1 ∈ Vweld n :=
      fun i hi => hroot i (by omega)
    intro a b cs ds hne
    by_cases hab : a = b
    · subst b
      apply diagonal_meet_bound hG hln _ (prefixLaw_nonneg K hK (m + 1)) a _ hM
        (fun x => forestLaw_marginal_cap hG hn hl parent root color (m + 1) hroot a x) cs ds
      exact hne.resolve_left (not_not.mpr rfl)
    · have hnew : ∀ (b : Fin m) (cs ds : List (Fin 3)),
          pairExpectation (prefixLaw K (m + 1)) (Fin.last m) b.castSucc
              (meet (l := l) (G := G) cs ds) ≤
            12 * ((n : ℝ) + 1) * (4 / (2 : ℝ) ^ n) := by
        intro b cs ds
        cases hpar : parent m with
        | none =>
          rw [pairExpectation_new_meet K m b (color m) (fun _ => root m)
            (fun z y => by simp only [K, forestKernel, hpar]) cs ds]
          calc
            _ ≤ ∑ z, prefixLaw K m z * (4 / (2 : ℝ) ^ n) := by
              apply Finset.sum_le_sum
              intro z _
              exact mul_le_mul_of_nonneg_left
                (meet_from_weld_le hG hn hl (color m) cs ds (root m) (z b)
                  (hroot m (Nat.lt_succ_self m) hpar)) (prefixLaw_nonneg K hK m z)
            _ = (∑ z, prefixLaw K m z) * (4 / (2 : ℝ) ^ n) :=
              (Finset.sum_mul _ _ _).symm
            _ ≤ 1 * (4 / (2 : ℝ) ^ n) := mul_le_mul_of_nonneg_right
              (prefixLaw_mass_le_one K hK hrow m) hM
            _ ≤ _ := by simpa only [one_mul] using hCM
        | some p =>
          rw [pairExpectation_new_meet K m b (color m) (fun z => z p)
            (fun z y => by simp only [K, forestKernel, hpar]) cs ds]
          exact ih hr p b (color m :: cs) ds (Or.inr (Or.inl (by simp)))
      by_cases ha : a = Fin.last m
      · subst a
        have hb : b ≠ Fin.last m := Ne.symm hab
        obtain ⟨b', rfl⟩ := Fin.exists_castSucc_eq.mpr hb
        exact hnew b' cs ds
      · obtain ⟨a', rfl⟩ := Fin.exists_castSucc_eq.mpr ha
        by_cases hb : b = Fin.last m
        · subst b
          rw [pairExpectation_meet_symm]
          exact hnew a' ds cs
        · obtain ⟨b', rfl⟩ := Fin.exists_castSucc_eq.mpr hb
          apply (pairExpectation_old_le K hK hrow m a' b'
            (meet (l := l) (G := G) cs ds) (meet_nonneg cs ds)).trans
          apply ih hr a' b' cs ds
          exact Or.inl (fun h => hab (congrArg Fin.castSucc h))

open Classical in
noncomputable def coincidence (w : (Fin m → X) → ℝ) (a b : Fin m) : ℝ :=
  ∑ z, if z a = z b then w z else 0

lemma coincidence_mono (w v : (Fin m → X) → ℝ) (h : ∀ z, w z ≤ v z)
    (a b : Fin m) : coincidence w a b ≤ coincidence v a b := by
  classical
  apply Finset.sum_le_sum
  intro z _
  split_ifs
  · exact h z
  · exact le_rfl

lemma coincidence_eq_meet (w : (Fin m → Label n) → ℝ) (a b : Fin m) :
    coincidence w a b = pairExpectation w a b (meet (l := l) (G := G) [] []) := by
  classical
  simp only [coincidence, pairExpectation, meet_nil_nil, mul_ite, mul_one, mul_zero]
  apply Finset.sum_congr rfl
  intro z _
  split_ifs <;> rfl

lemma forestLaw_collision_le (hG : G.IsValid) (hn : 2 ≤ n) (hl : 1 ≤ l) (hln : l ≤ n)
    (parent : (i : ℕ) → Option (Fin i)) (root : ℕ → Label n) (color : ℕ → Fin 3)
    (m : ℕ) (hroot : ∀ i < m, parent i = none → (root i).1 ∈ Vweld n)
    (a b : Fin m) (hab : a ≠ b) :
    coincidence (prefixLaw (forestKernel l G parent root color) m) a b ≤
      48 * ((n : ℝ) + 1) / (2 : ℝ) ^ n := by
  rw [coincidence_eq_meet (l := l) (G := G)]
  have hh := forest_meet_bound hG hn hl hln parent root color m hroot a b [] [] (Or.inl hab)
  convert hh using 1 <;> first | rfl | ring

lemma forestLaw_conditioned_collision_le (hG : G.IsValid) (hn : 16 ≤ n)
    (hl : 2 ≤ l) (hln : l ≤ n - 4)
    (parent : (i : ℕ) → Option (Fin i)) (root : ℕ → Label n) (color : ℕ → Fin 3)
    (m : ℕ) (hroot : ∀ i < m, parent i = none → (root i).1 ∈ Vweld n)
    (B : Finset ℕ) (hB : Vbd n l ⊆ B)
    (hsmall : (m : ℝ) * (B.card : ℝ) * (4 / (2 : ℝ) ^ n) ≤ 1 / 2)
    (a b : Fin m) (hab : a ≠ b) :
    coincidence (prefixLaw (maskKernel (forestKernel l G parent root color) (labelBoundary n B)) m) a b /
      (∑ z, prefixLaw (maskKernel (forestKernel l G parent root color) (labelBoundary n B)) m z)
        ≤ 96 * ((n : ℝ) + 1) / (2 : ℝ) ^ n := by
  let K := forestKernel l G parent root color
  let C := labelBoundary n B
  have hs := forestLaw_survival hG hn hl hln parent root color m hroot B hB
  have hz : (1 / 2 : ℝ) ≤ ∑ z, prefixLaw (maskKernel K C) m z := by linarith
  have hzpos : 0 < ∑ z, prefixLaw (maskKernel K C) m z := by linarith
  have hle := coincidence_mono _ _
    (masked_prefixLaw_le K C (forestKernel_nonneg l G parent root color) m) a b
  have hcap := forestLaw_collision_le (l := l) hG (by omega) (by omega) (by omega)
    parent root color m hroot a b hab
  apply (div_le_iff₀ hzpos).mpr
  calc
    _ ≤ 48 * ((n : ℝ) + 1) / (2 : ℝ) ^ n := hle.trans hcap
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left hz
        (by positivity : 0 ≤ 96 * ((n : ℝ) + 1) / (2 : ℝ) ^ n)
      convert hh using 1 <;> first | rfl | ring

end WeldedPath.Supplement.ForestCollision

end

-- Solutions.WeldedPathConnectedConcentration
section

namespace WeldedPath.Supplement.ConnectedConcentration

open Classical ConnectedReference FixedAvoidance ForestOrder ComponentProcess KappaForest ForestCollision
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}

noncomputable def sourceWeight (l : ℕ) (G : WeldedInstance n) (H : AbsForest n)
    (φ₀ : Fin H.k → Label n) (s : Fin H.k) (B : Finset ℕ) (φ : Fin H.k → Label n) : ℝ :=
  if H.Wfix φ s = H.Wfix φ₀ s ∧
      (∀ u, H.graph.Reachable s u → u ∉ H.Ctree φ s → (φ u).1 ∉ B)
  then H.muRef l G φ else 0

lemma sourceWeight_eq_fixedAvoidWeight (H : AbsForest n) (hH : H.IsValid)
    (φ₀ : Fin H.k → Label n) (s : Fin H.k) (hs : ∀ u, H.graph.Reachable s u)
    (B : Finset ℕ) (hB : Disjoint B (Vweld n)) (φ : Fin H.k → Label n) :
    sourceWeight l G H φ₀ s B φ = fixedAvoidWeight H φ₀ s l G B φ := by
  unfold sourceWeight fixedAvoidWeight
  simp only [connected_fixed_avoidance_iff H hH φ φ₀ s hs B hB,
    muRef_eq_muComp H s hs φ]

lemma stages_le_vertices (H : AbsForest n) (φ₀ : Fin H.k → Label n) (s : Fin H.k) :
    stages H φ₀ s ≤ H.k := by
  have h := Fintype.card_le_of_injective
    (fun u : freeVertices H φ₀ s => u.val) Subtype.val_injective
  simpa only [stages, Fintype.card_fin] using h

lemma comp_card_ne_one_of_free (H : AbsForest n) (φ₀ : Fin H.k → Label n)
    (s : Fin H.k) (hs : ∀ u, H.graph.Reachable s u) (u : Fin H.k)
    (hu : u ∉ H.Sfix φ₀ s) : (H.comp s).card ≠ 1 := by
  intro hc
  have hk : H.k = 1 := by
    simpa only [comp_eq_univ H s hs s, Finset.card_univ, Fintype.card_fin] using hc
  have hus : u = s := by
    apply Fin.ext
    have hi := u.isLt
    have hj := s.isLt
    omega
  subst u
  exact hu (FixedData.ctree_subset_sfix H φ₀ s (by simp [AbsForest.Ctree]))

lemma stages_budget (H : AbsForest n) (φ₀ : Fin H.k → Label n) (s : Fin H.k)
    (B : Finset ℕ)
    (hsmall : (H.k : ℝ) * (B.card : ℝ) * (4 / (2 : ℝ) ^ n) ≤ 1 / 2) :
    (stages H φ₀ s : ℝ) * (B.card : ℝ) * (4 / (2 : ℝ) ^ n) ≤ 1 / 2 := by
  have hk : (stages H φ₀ s : ℝ) ≤ H.k := by exact_mod_cast stages_le_vertices H φ₀ s
  exact (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hk (by positivity)) (by positivity)).trans hsmall

lemma conditional_source_event_eq_process (H : AbsForest n) (hH : H.IsValid)
    (φ₀ : Fin H.k → Label n) (s : Fin H.k) (hs : ∀ u, H.graph.Reachable s u)
    (C : ParentOrder H φ₀ s) (hG : G.IsValid)
    (hsize : (H.comp s).card ≠ 1) (hμ : H.muRef l G φ₀ ≠ 0)
    (B : Finset ℕ) (hB : Disjoint B (Vweld n))
    (event : (Fin (stages H φ₀ s) → Label n) → Prop) :
    (∑ φ, if event (fun i => φ (C.order i).val) then sourceWeight l G H φ₀ s B φ else 0) /
      (∑ φ, sourceWeight l G H φ₀ s B φ) =
    (∑ z, if event z then maskedLaw H φ₀ s C l G B z else 0) /
      (∑ z, maskedLaw H φ₀ s C l G B z) := by
  simp_rw [sourceWeight_eq_fixedAvoidWeight H hH φ₀ s hs B hB]
  exact conditional_event_eq_process H φ₀ s C l G hG (comp_eq_univ H s hs s) hsize
    (muComp_ne_zero_of_muRef_ne_zero H s hs φ₀ hμ) B event

theorem conditional_free_point_bound (H : AbsForest n) (hH : H.IsValid)
    (φ₀ : Fin H.k → Label n) (s : Fin H.k) (hs : ∀ u, H.graph.Reachable s u)
    (hG : G.IsValid) (hn : 16 ≤ n) (hl : 2 ≤ l) (hln : l ≤ n - 4)
    (hμ : H.muRef l G φ₀ ≠ 0) (B : Finset ℕ)
    (hB : Vbd n l ⊆ B) (hBw : Disjoint B (Vweld n))
    (hsmall : (H.k : ℝ) * (B.card : ℝ) * (4 / (2 : ℝ) ^ n) ≤ 1 / 2)
    (u : Fin H.k) (hu : u ∉ H.Sfix φ₀ s) (x : Label n) :
    (∑ φ, if φ u = x then sourceWeight l G H φ₀ s B φ else 0) /
      (∑ φ, sourceWeight l G H φ₀ s B φ) ≤ 8 / (2 : ℝ) ^ n := by
  obtain ⟨C⟩ := exists_parent_order H hH φ₀ s
  let v : freeVertices H φ₀ s := ⟨u, Finset.mem_sdiff.mpr
    ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs u⟩, hu⟩⟩
  let j := C.order.symm v
  have he := conditional_source_event_eq_process H hH φ₀ s hs C hG
    (comp_card_ne_one_of_free H φ₀ s hs u hu) hμ B hBw (fun z => z j = x)
  have hb := forestLaw_conditioned_marginal_cap hG hn hl hln
    (processParent H φ₀ s C) (processRoot H φ₀ s C) (processColor H φ₀ s C)
    (stages H φ₀ s) (process_root_weld H φ₀ s C) B hB
    (stages_budget H φ₀ s B hsmall) j x
  have h := he.trans_le hb
  simpa only [j, Equiv.apply_symm_apply, v] using h

theorem conditional_free_pair_collision_bound (H : AbsForest n) (hH : H.IsValid)
    (φ₀ : Fin H.k → Label n) (s : Fin H.k) (hs : ∀ u, H.graph.Reachable s u)
    (hG : G.IsValid) (hn : 16 ≤ n) (hl : 2 ≤ l) (hln : l ≤ n - 4)
    (hμ : H.muRef l G φ₀ ≠ 0) (B : Finset ℕ)
    (hB : Vbd n l ⊆ B) (hBw : Disjoint B (Vweld n))
    (hsmall : (H.k : ℝ) * (B.card : ℝ) * (4 / (2 : ℝ) ^ n) ≤ 1 / 2)
    (u v : Fin H.k) (hu : u ∉ H.Sfix φ₀ s) (hv : v ∉ H.Sfix φ₀ s) (huv : u ≠ v) :
    (∑ φ, if φ u = φ v then sourceWeight l G H φ₀ s B φ else 0) /
      (∑ φ, sourceWeight l G H φ₀ s B φ) ≤ 96 * ((n : ℝ) + 1) / (2 : ℝ) ^ n := by
  obtain ⟨C⟩ := exists_parent_order H hH φ₀ s
  let a : freeVertices H φ₀ s := ⟨u, Finset.mem_sdiff.mpr
    ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs u⟩, hu⟩⟩
  let b : freeVertices H φ₀ s := ⟨v, Finset.mem_sdiff.mpr
    ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs v⟩, hv⟩⟩
  let i := C.order.symm a
  let j := C.order.symm b
  have hij : i ≠ j := by
    intro h
    have hh := congrArg (fun k => (C.order k).val) h
    simp only [i, j, Equiv.apply_symm_apply] at hh
    exact huv hh
  have he := conditional_source_event_eq_process H hH φ₀ s hs C hG
    (comp_card_ne_one_of_free H φ₀ s hs u hu) hμ B hBw (fun z => z i = z j)
  have hb := forestLaw_conditioned_collision_le hG hn hl hln
    (processParent H φ₀ s C) (processRoot H φ₀ s C) (processColor H φ₀ s C)
    (stages H φ₀ s) (process_root_weld H φ₀ s C) B hB
    (stages_budget H φ₀ s B hsmall) i j hij
  have h := he.trans_le hb
  simpa only [i, j, Equiv.apply_symm_apply, a, b] using h

end WeldedPath.Supplement.ConnectedConcentration

end

-- Solutions.WeldedPathConditionalInjectivity
section

namespace WeldedPath.Supplement.ConditionalInjectivity

open Classical ConnectedConcentration
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}

lemma sourceWeight_nonneg (H : AbsForest n) (hH : H.IsValid)
    (φ₀ : Fin H.k → Label n) (s : Fin H.k) (B : Finset ℕ)
    (φ : Fin H.k → Label n) : 0 ≤ sourceWeight l G H φ₀ s B φ := by
  unfold sourceWeight
  split_ifs
  · exact ForestFactorization.muRef_nonneg l G H hH φ
  · exact le_rfl

lemma sourceWeight_agree (H : AbsForest n) (hH : H.IsValid)
    (φ₀ φ : Fin H.k → Label n) (s : Fin H.k) (B : Finset ℕ)
    (hw : sourceWeight l G H φ₀ s B φ ≠ 0) :
    ∀ v ∈ H.Sfix φ₀ s, φ v = φ₀ v := by
  have hf : H.Wfix φ s = H.Wfix φ₀ s := by
    unfold sourceWeight at hw
    split_ifs at hw with h
    · exact h.1
    · exact (hw rfl).elim
  exact (FixedData.wfix_eq_iff_agree_sfix H hH φ φ₀ s).mp hf

lemma fixed_collision_eq_point (H : AbsForest n) (hH : H.IsValid)
    (φ₀ : Fin H.k → Label n) (s : Fin H.k) (B : Finset ℕ)
    (u v : Fin H.k) (hv : v ∈ H.Sfix φ₀ s) :
    (∑ φ, if φ u = φ v then sourceWeight l G H φ₀ s B φ else 0) =
      ∑ φ, if φ u = φ₀ v then sourceWeight l G H φ₀ s B φ else 0 := by
  apply Finset.sum_congr rfl
  intro φ _
  by_cases hw : sourceWeight l G H φ₀ s B φ = 0
  · simp only [hw, ite_self]
  · rw [sourceWeight_agree H hH φ₀ φ s B hw v hv]

theorem conditional_free_fixed_collision_bound (H : AbsForest n) (hH : H.IsValid)
    (φ₀ : Fin H.k → Label n) (s : Fin H.k) (hs : ∀ u, H.graph.Reachable s u)
    (hG : G.IsValid) (hn : 16 ≤ n) (hl : 2 ≤ l) (hln : l ≤ n - 4)
    (hμ : H.muRef l G φ₀ ≠ 0) (B : Finset ℕ)
    (hB : Vbd n l ⊆ B) (hBw : Disjoint B (Vweld n))
    (hsmall : (H.k : ℝ) * (B.card : ℝ) * (4 / (2 : ℝ) ^ n) ≤ 1 / 2)
    (u v : Fin H.k) (hu : u ∉ H.Sfix φ₀ s) (hv : v ∈ H.Sfix φ₀ s) :
    (∑ φ, if φ u = φ v then sourceWeight l G H φ₀ s B φ else 0) /
      (∑ φ, sourceWeight l G H φ₀ s B φ) ≤ 8 / (2 : ℝ) ^ n := by
  rw [fixed_collision_eq_point H hH φ₀ s B u v hv]
  exact conditional_free_point_bound H hH φ₀ s hs hG hn hl hln hμ B hB hBw hsmall u hu _

theorem conditional_pair_collision_bound_of_free (H : AbsForest n) (hH : H.IsValid)
    (φ₀ : Fin H.k → Label n) (s : Fin H.k) (hs : ∀ u, H.graph.Reachable s u)
    (hG : G.IsValid) (hn : 16 ≤ n) (hl : 2 ≤ l) (hln : l ≤ n - 4)
    (hμ : H.muRef l G φ₀ ≠ 0) (B : Finset ℕ)
    (hB : Vbd n l ⊆ B) (hBw : Disjoint B (Vweld n))
    (hsmall : (H.k : ℝ) * (B.card : ℝ) * (4 / (2 : ℝ) ^ n) ≤ 1 / 2)
    (u v : Fin H.k) (huv : u ≠ v)
    (hfree : u ∉ H.Sfix φ₀ s ∨ v ∉ H.Sfix φ₀ s) :
    (∑ φ, if φ u = φ v then sourceWeight l G H φ₀ s B φ else 0) /
      (∑ φ, sourceWeight l G H φ₀ s B φ) ≤ 96 * ((n : ℝ) + 1) / (2 : ℝ) ^ n := by
  have hconst : 8 / (2 : ℝ) ^ n ≤ 96 * ((n : ℝ) + 1) / (2 : ℝ) ^ n := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hn0 : (0 : ℝ) ≤ n := by positivity
    nlinarith
  by_cases hu : u ∈ H.Sfix φ₀ s
  · have hv : v ∉ H.Sfix φ₀ s := hfree.resolve_left (not_not.mpr hu)
    have he : (∑ φ, if φ u = φ v then sourceWeight l G H φ₀ s B φ else 0) =
        ∑ φ, if φ v = φ u then sourceWeight l G H φ₀ s B φ else 0 := by
      apply Finset.sum_congr rfl
      intro φ _
      simp only [eq_comm]
    rw [he]
    exact (conditional_free_fixed_collision_bound H hH φ₀ s hs hG hn hl hln hμ
      B hB hBw hsmall v u hv hu).trans hconst
  · by_cases hv : v ∈ H.Sfix φ₀ s
    · exact (conditional_free_fixed_collision_bound H hH φ₀ s hs hG hn hl hln hμ
        B hB hBw hsmall u v hu hv).trans hconst
    · exact conditional_free_pair_collision_bound H hH φ₀ s hs hG hn hl hln hμ
        B hB hBw hsmall u v hu hv huv

theorem conditional_pair_collision_bound (H : AbsForest n) (hH : H.IsValid)
    (φ₀ : Fin H.k → Label n) (s : Fin H.k) (hs : ∀ u, H.graph.Reachable s u)
    (hG : G.IsValid) (hn : 16 ≤ n) (hl : 2 ≤ l) (hln : l ≤ n - 4)
    (hμ : H.muRef l G φ₀ ≠ 0) (B : Finset ℕ)
    (hB : Vbd n l ⊆ B) (hBw : Disjoint B (Vweld n))
    (hsmall : (H.k : ℝ) * (B.card : ℝ) * (4 / (2 : ℝ) ^ n) ≤ 1 / 2)
    (hfix : Set.InjOn φ₀ (H.Sfix φ₀ s)) (u v : Fin H.k) (huv : u ≠ v) :
    (∑ φ, if φ u = φ v then sourceWeight l G H φ₀ s B φ else 0) /
      (∑ φ, sourceWeight l G H φ₀ s B φ) ≤ 96 * ((n : ℝ) + 1) / (2 : ℝ) ^ n := by
  have hconst : 8 / (2 : ℝ) ^ n ≤ 96 * ((n : ℝ) + 1) / (2 : ℝ) ^ n := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hn0 : (0 : ℝ) ≤ n := by positivity
    nlinarith
  by_cases hu : u ∈ H.Sfix φ₀ s
  · by_cases hv : v ∈ H.Sfix φ₀ s
    · have hz : (∑ φ, if φ u = φ v then sourceWeight l G H φ₀ s B φ else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro φ _
        by_cases hw : sourceWeight l G H φ₀ s B φ = 0
        · simp only [hw, ite_self]
        · have ha := sourceWeight_agree H hH φ₀ φ s B hw
          have he : φ u ≠ φ v := by
            rw [ha u hu, ha v hv]
            exact fun h => huv (hfix hu hv h)
          exact if_neg he
      rw [hz, zero_div]
      positivity
    · have he : (∑ φ, if φ u = φ v then sourceWeight l G H φ₀ s B φ else 0) =
          ∑ φ, if φ v = φ u then sourceWeight l G H φ₀ s B φ else 0 := by
        apply Finset.sum_congr rfl
        intro φ _
        simp only [eq_comm]
      rw [he]
      exact (conditional_free_fixed_collision_bound H hH φ₀ s hs hG hn hl hln hμ
        B hB hBw hsmall v u hv hu).trans hconst
  · by_cases hv : v ∈ H.Sfix φ₀ s
    · exact (conditional_free_fixed_collision_bound H hH φ₀ s hs hG hn hl hln hμ
        B hB hBw hsmall u v hu hv).trans hconst
    · exact conditional_free_pair_collision_bound H hH φ₀ s hs hG hn hl hln hμ
        B hB hBw hsmall u v hu hv huv

lemma weighted_exists_le_sum {A I : Type*} [Fintype A] [Fintype I]
    (w : A → ℝ) (hw : ∀ a, 0 ≤ w a) (E : I → A → Prop) :
    (∑ a, if ∃ i, E i a then w a else 0) ≤ ∑ i, ∑ a, if E i a then w a else 0 := by
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro a _
  by_cases h : ∃ i, E i a
  · rw [if_pos h]
    obtain ⟨i, hi⟩ := h
    calc
      w a = if E i a then w a else 0 := (if_pos hi).symm
      _ ≤ ∑ j, if E j a then w a else 0 :=
        Finset.single_le_sum (f := fun j => if E j a then w a else 0)
          (fun j _ => by split_ifs <;> first | exact hw a | exact le_rfl)
          (Finset.mem_univ i)
  · rw [if_neg h]
    exact Finset.sum_nonneg (fun i _ => by split_ifs <;> first | exact hw a | exact le_rfl)

theorem conditional_noninjective_bound (H : AbsForest n) (hH : H.IsValid)
    (φ₀ : Fin H.k → Label n) (s : Fin H.k) (hs : ∀ u, H.graph.Reachable s u)
    (hG : G.IsValid) (hn : 16 ≤ n) (hl : 2 ≤ l) (hln : l ≤ n - 4)
    (hμ : H.muRef l G φ₀ ≠ 0) (B : Finset ℕ)
    (hB : Vbd n l ⊆ B) (hBw : Disjoint B (Vweld n))
    (hsmall : (H.k : ℝ) * (B.card : ℝ) * (4 / (2 : ℝ) ^ n) ≤ 1 / 2)
    (hfix : Set.InjOn φ₀ (H.Sfix φ₀ s)) :
    (∑ φ, if ¬Function.Injective φ then sourceWeight l G H φ₀ s B φ else 0) /
      (∑ φ, sourceWeight l G H φ₀ s B φ) ≤
        96 * ((n : ℝ) + 1) * (H.k : ℝ) ^ 2 / (2 : ℝ) ^ n := by
  let w := sourceWeight l G H φ₀ s B
  have hw : ∀ φ, 0 ≤ w φ := sourceWeight_nonneg H hH φ₀ s B
  have hden : 0 ≤ ∑ φ, w φ := Finset.sum_nonneg (fun φ _ => hw φ)
  let E : (Fin H.k × Fin H.k) → (Fin H.k → Label n) → Prop :=
    fun p φ => p.1 ≠ p.2 ∧ φ p.1 = φ p.2
  have hbad (φ : Fin H.k → Label n) :
      (∃ p, E p φ) ↔ ¬Function.Injective φ := by
    constructor
    · rintro ⟨⟨u, v⟩, huv, he⟩ hi
      exact huv (hi he)
    · intro hi
      by_contra hh
      apply hi
      intro u v he
      by_contra huv
      exact hh ⟨(u, v), huv, he⟩
  have hu := weighted_exists_le_sum w hw E
  simp_rw [hbad] at hu
  have hu' : (∑ φ, if ¬Function.Injective φ then w φ else 0) ≤
      ∑ p, ∑ φ, if E p φ then w φ else 0 := by
    convert hu using 1
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro φ _
    split_ifs <;> rfl
  have hp (p : Fin H.k × Fin H.k) :
      (∑ φ, if E p φ then w φ else 0) / (∑ φ, w φ) ≤
        96 * ((n : ℝ) + 1) / (2 : ℝ) ^ n := by
    by_cases he : p.1 = p.2
    · simp only [E, he, ne_eq, not_true_eq_false, false_and, if_false,
        Finset.sum_const_zero, zero_div]
      positivity
    · have hs' : (∑ φ, if E p φ then w φ else 0) =
          ∑ φ, if φ p.1 = φ p.2 then w φ else 0 := by
        apply Finset.sum_congr rfl
        intro φ _
        simp only [E, he, ne_eq, not_false_eq_true, true_and]
      rw [hs']
      exact conditional_pair_collision_bound H hH φ₀ s hs hG hn hl hln hμ
        B hB hBw hsmall hfix p.1 p.2 he
  calc
    _ ≤ (∑ p, ∑ φ, if E p φ then w φ else 0) / (∑ φ, w φ) :=
      div_le_div_of_nonneg_right hu' hden
    _ = ∑ p, (∑ φ, if E p φ then w φ else 0) / (∑ φ, w φ) :=
      Finset.sum_div _ _ _
    _ ≤ ∑ _p : Fin H.k × Fin H.k, 96 * ((n : ℝ) + 1) / (2 : ℝ) ^ n :=
      Finset.sum_le_sum (fun p _ => hp p)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul]
      ring

end WeldedPath.Supplement.ConditionalInjectivity

end

-- Solutions.WeldedPathFixedCollisions
section

namespace WeldedPath.Supplement.FixedCollisions

open scoped BigOperators
open Classical WeldedPath.WeightedCoefficients WeldedPath.HilbertSupport

variable {n : ℕ}

def Collision (H : AbsForest n) (a b : Fin H.k) (φ : Fin H.k → Label n) : Prop :=
  a ≠ b ∧ φ a = φ b

def FixedCollision (H : AbsForest n) (v a b : Fin H.k) (φ : Fin H.k → Label n) : Prop :=
  Collision H a b φ ∧ a ∈ H.Sfix φ v ∧ b ∈ H.Sfix φ v

def FreeCollision (H : AbsForest n) (v a b : Fin H.k) (φ : Fin H.k → Label n) : Prop :=
  Collision H a b φ ∧ ¬(a ∈ H.Sfix φ v ∧ b ∈ H.Sfix φ v)

lemma sfix_eq_of_wfix_eq (H : AbsForest n) (hH : H.IsValid)
    (v : Fin H.k) (φ ψ : Fin H.k → Label n) (hd : H.Wfix φ v = H.Wfix ψ v) :
    H.Sfix φ v = H.Sfix ψ v :=
  FixedData.sfix_eq_of_agree_sfix H hH φ ψ v
    ((FixedData.wfix_eq_iff_agree_sfix H hH φ ψ v).mp hd)

/-- Fixed collisions are measurable using the recorded fixed data alone. -/
theorem fixedCollision_factors (H : AbsForest n) (hH : H.IsValid)
    (v a b : Fin H.k) :
    Function.FactorsThrough (FixedCollision H v a b) (fun φ => H.Wfix φ v) := by
  intro φ ψ hd
  apply propext
  have hs := sfix_eq_of_wfix_eq H hH v φ ψ hd
  have ha := (FixedData.wfix_eq_iff_agree_sfix H hH φ ψ v).mp hd
  constructor
  · rintro ⟨⟨hne, he⟩, hfa, hfb⟩
    have hga : a ∈ H.Sfix ψ v := hs ▸ hfa
    have hgb : b ∈ H.Sfix ψ v := hs ▸ hfb
    exact ⟨⟨hne, (ha a hga).symm.trans (he.trans (ha b hgb))⟩, hga, hgb⟩
  · rintro ⟨⟨hne, he⟩, hga, hgb⟩
    exact ⟨⟨hne, (ha a hga).trans (he.trans (ha b hgb).symm)⟩,
      hs.symm ▸ hga, hs.symm ▸ hgb⟩

lemma dataSpace_mask_closed {Ω D : Type*} [Fintype Ω] [DecidableEq Ω]
    (μ : Ω → ℝ) (data : Ω → D) (P : Ω → Prop)
    (hP : Function.FactorsThrough P data) (f : Hil Ω) (hf : f ∈ dataSpace μ data) :
    (eventSpace P).starProjection f ∈ dataSpace μ data := by
  obtain ⟨Q, hQ⟩ := (Function.factorsThrough_iff P).mp hP
  obtain ⟨h, rfl⟩ := (mem_dataSpace μ data f).mp hf
  apply (mem_dataSpace μ data _).mpr
  refine ⟨fun d => if Q d then h d else 0, ?_⟩
  rw [eventSpace_projection]
  ext ω
  simp only [diagProj_apply]
  have hQω : P ω = Q (data ω) := congrFun hQ ω
  change (Real.sqrt (μ ω) : ℂ) * (if Q (data ω) then h (data ω) else 0) =
    (if P ω then (Real.sqrt (μ ω) : ℂ) * h (data ω) else 0)
  rw [hQω]
  simp only [mul_ite, mul_zero]

theorem fixed_mask_mem_local (H : AbsForest n) (hH : H.IsValid)
    (μ : (Fin H.k → Label n) → ℝ) (v a b : Fin H.k)
    (f : Hil (Fin H.k → Label n)) (hf : f ∈ localCoefficientSpace H μ v) :
    (eventSpace (FixedCollision H v a b)).starProjection f ∈ localCoefficientSpace H μ v :=
  dataSpace_mask_closed μ (fun φ => H.Wfix φ v) (FixedCollision H v a b)
    (fixedCollision_factors H hH v a b) f hf

lemma event_projection_mem_of_imp {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P Q : Ω → Prop) (hPQ : ∀ ω, P ω → Q ω) (f : Hil Ω) :
    (eventSpace P).starProjection f ∈ eventSpace Q := by
  intro ω hω
  rw [eventSpace_projection]
  simp only [diagProj_apply, if_neg (mt (hPQ ω) hω)]

theorem fixed_mask_mem_collision (H : AbsForest n) (v a b : Fin H.k)
    (f : Hil (Fin H.k → Label n)) :
    (eventSpace (FixedCollision H v a b)).starProjection f ∈ eventSpace (Collision H a b) :=
  event_projection_mem_of_imp _ _ (fun _ h => h.1) f

theorem fixed_mask_mem_kernel (H : AbsForest n) (hH : H.IsValid)
    (μ : (Fin H.k → Label n) → ℝ) (v a b : Fin H.k)
    (f : Hil (Fin H.k → Label n)) (hf : f ∈ localCoefficientSpace H μ v) :
    (eventSpace (FixedCollision H v a b)).starProjection f ∈
      (⨆ v, localCoefficientSpace H μ v) ⊓ (eventSpace Function.Injective)ᗮ := by
  constructor
  · exact (le_iSup (fun v => localCoefficientSpace H μ v) v)
      (fixed_mask_mem_local H hH μ v a b f hf)
  · rw [eventSpace_orthogonal]
    apply event_projection_mem_of_imp
    intro φ hfix hinj
    exact hfix.1.1 (hinj hfix.1.2)

theorem collision_projection_split (H : AbsForest n) (v a b : Fin H.k)
    (f : Hil (Fin H.k → Label n)) :
    (eventSpace (Collision H a b)).starProjection f =
      (eventSpace (FixedCollision H v a b)).starProjection f +
      (eventSpace (FreeCollision H v a b)).starProjection f := by
  simp only [eventSpace_projection]
  ext φ
  simp only [PiLp.add_apply, diagProj_apply]
  change (if Collision H a b φ then f φ else 0) =
    (if FixedCollision H v a b φ then f φ else 0) +
    (if FreeCollision H v a b φ then f φ else 0)
  by_cases hc : Collision H a b φ
  · by_cases hf : a ∈ H.Sfix φ v ∧ b ∈ H.Sfix φ v
    · simp [FixedCollision, FreeCollision, hc, hf, hf.1, hf.2]
    · simp only [FixedCollision, FreeCollision, hc, true_and, hf, not_false_eq_true,
        ite_true, ite_false, zero_add]
  · simp [FixedCollision, FreeCollision, hc]

theorem not_injective_iff_collision (H : AbsForest n) (φ : Fin H.k → Label n) :
    ¬Function.Injective φ ↔ ∃ p : Fin H.k × Fin H.k, Collision H p.1 p.2 φ := by
  constructor
  · intro hi
    simp only [Function.Injective] at hi
    push_neg at hi
    obtain ⟨a, b, hab, hne⟩ := hi
    exact ⟨(a, b), hne, hab⟩
  · rintro ⟨⟨a, b⟩, hne, hab⟩ hi
    exact hne (hi hab)

end WeldedPath.Supplement.FixedCollisions

end

-- Solutions.WeldedPathSourceFiberBound
section

namespace WeldedPath.Supplement.SourceFiberBound

open Classical ConnectedConcentration FixedData
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}

theorem free_collision_fiber_bound (H : AbsForest n) (hH : H.IsValid)
    (mu : (Fin H.k → Label n) → ℝ)
    (hmu : ∀ φ, 0 ≤ mu φ)
    (s : Fin H.k) (hs : ∀ u, H.graph.Reachable s u)
    (hG : G.IsValid) (hn : 16 ≤ n) (hl : 2 ≤ l) (hln : l ≤ n - 4)
    (B : Finset ℕ) (hB : Vbd n l ⊆ B) (hBw : Disjoint B (Vweld n))
    (hsmall : (H.k : ℝ) * (B.card : ℝ) * (4 / (2 : ℝ) ^ n) ≤ 1 / 2)
    (hsource : ∀ φ₀, 0 < mu φ₀ →
      H.muRef l G φ₀ ≠ 0 ∧
      ∀ φ, (if H.Wfix φ s = H.Wfix φ₀ s then mu φ else 0) =
        sourceWeight l G H φ₀ s B φ)
    (a b : Fin H.k) (d : FixedDataFunctions.Data H) :
    (∑ φ, if H.Wfix φ s = d ∧ FixedCollisions.FreeCollision H s a b φ then
      mu φ else 0) ≤
      (96 * ((n : ℝ) + 1) / (2 : ℝ) ^ n) *
        ∑ φ, if H.Wfix φ s = d then mu φ else 0 := by
  let μ := mu
  have hμ : ∀ φ, 0 ≤ μ φ := hmu
  have hden : 0 ≤ ∑ φ, if H.Wfix φ s = d then μ φ else 0 :=
    Finset.sum_nonneg fun φ _ => by split_ifs; exact hμ φ; rfl
  by_cases hab : a = b
  · simp only [hab, FixedCollisions.FreeCollision, FixedCollisions.Collision,
      ne_eq, not_true_eq_false, false_and, and_false, ite_false, Finset.sum_const_zero]
    exact mul_nonneg (by positivity) hden
  by_cases hwit : ∃ φ, H.Wfix φ s = d ∧ 0 < μ φ
  · obtain ⟨φ₀, hd₀, hpos⟩ := hwit
    obtain ⟨href, hsrcEq⟩ := hsource _ hpos
    have heq (φ : Fin H.k → Label n) :
        (if H.Wfix φ s = d then μ φ else 0) = sourceWeight l G H φ₀ s B φ := by
      rw [← hd₀]
      exact hsrcEq φ
    by_cases hfixed : a ∈ H.Sfix φ₀ s ∧ b ∈ H.Sfix φ₀ s
    · have hzero : (∑ φ, if H.Wfix φ s = d ∧ FixedCollisions.FreeCollision H s a b φ
          then μ φ else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro φ _
        apply if_neg
        rintro ⟨hφ, hfree⟩
        have hS := FixedCollisions.sfix_eq_of_wfix_eq H hH s φ φ₀ (hφ.trans hd₀.symm)
        exact hfree.2 ⟨hS.symm ▸ hfixed.1, hS.symm ▸ hfixed.2⟩
      change (∑ φ, if H.Wfix φ s = d ∧ FixedCollisions.FreeCollision H s a b φ
        then μ φ else 0) ≤ _
      rw [hzero]
      exact mul_nonneg (by positivity) hden
    · have hfree : a ∉ H.Sfix φ₀ s ∨ b ∉ H.Sfix φ₀ s := not_and_or.mp hfixed
      have hbnd := ConditionalInjectivity.conditional_pair_collision_bound_of_free
        H hH φ₀ s hs hG hn hl hln href B hB hBw hsmall a b hab hfree
      have hsrc : ∀ φ, 0 ≤ sourceWeight l G H φ₀ s B φ := by
        intro φ
        rw [← heq φ]
        split_ifs
        · exact hμ φ
        · rfl
      have hD : 0 < ∑ φ, sourceWeight l G H φ₀ s B φ := by
        have hpos' : 0 < sourceWeight l G H φ₀ s B φ₀ := by
          rw [← heq φ₀, if_pos hd₀]
          exact hpos
        exact hpos'.trans_le (Finset.single_le_sum (fun φ _ => hsrc φ) (Finset.mem_univ φ₀))
      calc
        _ ≤ ∑ φ, if H.Wfix φ s = d ∧ φ a = φ b then μ φ else 0 := by
          apply Finset.sum_le_sum
          intro φ _
          by_cases hp : H.Wfix φ s = d ∧ FixedCollisions.FreeCollision H s a b φ
          · rw [if_pos hp, if_pos ⟨hp.1, hp.2.1.2⟩]
          · rw [if_neg hp]
            split_ifs
            · exact hμ φ
            · rfl
        _ = ∑ φ, if φ a = φ b then sourceWeight l G H φ₀ s B φ else 0 := by
          apply Finset.sum_congr rfl
          intro φ _
          rw [← heq φ]
          split_ifs <;> simp_all
        _ ≤ (96 * ((n : ℝ) + 1) / (2 : ℝ) ^ n) *
            ∑ φ, sourceWeight l G H φ₀ s B φ := (div_le_iff₀ hD).mp hbnd
        _ = _ := by simp_rw [← heq]; rfl
  · have hz : ∀ φ, H.Wfix φ s = d → μ φ = 0 := by
      intro φ hd
      exact le_antisymm (le_of_not_gt (fun hp => hwit ⟨φ, hd, hp⟩)) (hμ φ)
    have hnum : (∑ φ, if H.Wfix φ s = d ∧ FixedCollisions.FreeCollision H s a b φ
        then μ φ else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro φ _
      by_cases hd : H.Wfix φ s = d
      · simp only [hz φ hd, ite_self]
      · simp only [hd, false_and, ite_false]
    change (∑ φ, if H.Wfix φ s = d ∧ FixedCollisions.FreeCollision H s a b φ
      then μ φ else 0) ≤ _
    rw [hnum]
    exact mul_nonneg (by positivity) hden


theorem free_point_fiber_bound (H : AbsForest n) (hH : H.IsValid)
    (mu : (Fin H.k → Label n) → ℝ) (hmu : ∀ φ, 0 ≤ mu φ)
    (s : Fin H.k) (hs : ∀ u, H.graph.Reachable s u)
    (hG : G.IsValid) (hn : 16 ≤ n) (hl : 2 ≤ l) (hln : l ≤ n - 4)
    (B : Finset ℕ) (hB : Vbd n l ⊆ B) (hBw : Disjoint B (Vweld n))
    (hsmall : (H.k : ℝ) * (B.card : ℝ) * (4 / (2 : ℝ) ^ n) ≤ 1 / 2)
    (hsource : ∀ φ₀, 0 < mu φ₀ → H.muRef l G φ₀ ≠ 0 ∧
      ∀ φ, (if H.Wfix φ s = H.Wfix φ₀ s then mu φ else 0) = sourceWeight l G H φ₀ s B φ)
    (a : Fin H.k) (x : Label n) (d : FixedDataFunctions.Data H) :
    (∑ φ, if H.Wfix φ s = d ∧ a ∉ H.Sfix φ s ∧ φ a = x then mu φ else 0) ≤
      (8 / (2 : ℝ) ^ n) * ∑ φ, if H.Wfix φ s = d then mu φ else 0 := by
  have hden : 0 ≤ ∑ φ, if H.Wfix φ s = d then mu φ else 0 :=
    Finset.sum_nonneg fun φ _ => by split_ifs; exact hmu φ; rfl
  by_cases hwit : ∃ φ, H.Wfix φ s = d ∧ 0 < mu φ
  · obtain ⟨φ₀, hd₀, hpos⟩ := hwit
    obtain ⟨href, hsrcEq⟩ := hsource _ hpos
    have heq (φ : Fin H.k → Label n) :
        (if H.Wfix φ s = d then mu φ else 0) = sourceWeight l G H φ₀ s B φ := by
      rw [← hd₀]
      exact hsrcEq φ
    by_cases ha : a ∈ H.Sfix φ₀ s
    · have hz : (∑ φ, if H.Wfix φ s = d ∧ a ∉ H.Sfix φ s ∧ φ a = x then mu φ else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro φ _
        apply if_neg
        rintro ⟨hd, hn, _⟩
        have hS := FixedCollisions.sfix_eq_of_wfix_eq H hH s φ φ₀ (hd.trans hd₀.symm)
        exact hn (hS.symm ▸ ha)
      rw [hz]
      exact mul_nonneg (by positivity) hden
    · have hbnd := conditional_free_point_bound H hH φ₀ s hs hG hn hl hln href
        B hB hBw hsmall a ha x
      have hsrc : ∀ φ, 0 ≤ sourceWeight l G H φ₀ s B φ := by
        intro φ
        rw [← heq φ]
        split_ifs
        · exact hmu φ
        · rfl
      have hD : 0 < ∑ φ, sourceWeight l G H φ₀ s B φ := by
        have hpos' : 0 < sourceWeight l G H φ₀ s B φ₀ := by
          rw [← heq φ₀, if_pos hd₀]
          exact hpos
        exact hpos'.trans_le (Finset.single_le_sum (fun φ _ => hsrc φ) (Finset.mem_univ φ₀))
      calc
        _ ≤ ∑ φ, if H.Wfix φ s = d ∧ φ a = x then mu φ else 0 := by
          apply Finset.sum_le_sum
          intro φ _
          by_cases hp : H.Wfix φ s = d ∧ a ∉ H.Sfix φ s ∧ φ a = x
          · rw [if_pos hp, if_pos ⟨hp.1, hp.2.2⟩]
          · rw [if_neg hp]
            split_ifs
            · exact hmu φ
            · rfl
        _ = ∑ φ, if φ a = x then sourceWeight l G H φ₀ s B φ else 0 := by
          apply Finset.sum_congr rfl
          intro φ _
          rw [← heq φ]
          split_ifs <;> simp_all
        _ ≤ (8 / (2 : ℝ) ^ n) * ∑ φ, sourceWeight l G H φ₀ s B φ :=
          (div_le_iff₀ hD).mp hbnd
        _ = _ := by simp_rw [← heq]
  · have hz : ∀ φ, H.Wfix φ s = d → mu φ = 0 := by
      intro φ hd
      exact le_antisymm (le_of_not_gt (fun hp => hwit ⟨φ, hd, hp⟩)) (hmu φ)
    have hnum : (∑ φ, if H.Wfix φ s = d ∧ a ∉ H.Sfix φ s ∧ φ a = x then mu φ else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro φ _
      by_cases hd : H.Wfix φ s = d
      · simp only [hz φ hd, ite_self]
      · simp only [hd, false_and, ite_false]
    rw [hnum]
    exact mul_nonneg (by positivity) hden

end WeldedPath.Supplement.SourceFiberBound

end

-- Solutions.WeldedPathBoundarySector
section

namespace WeldedPath.Supplement.BoundarySector

open Classical BoundaryCoefficients FixedData ConnectedConcentration FixedCollisions
open WeldedPath.WeightedCoefficients WeldedPath.HilbertSupport
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}

def boundaryPattern (H : AbsForest n) (B : Finset ℕ) (F : Finset (Fin H.k))
    (φ : Fin H.k → Label n) : Prop := ∀ u, (φ u).val ∈ B ↔ u ∈ F

noncomputable def sectorWeight (l : ℕ) (G : WeldedInstance n) (H : AbsForest n)
    (B : Finset ℕ) (F : Finset (Fin H.k)) (φ : Fin H.k → Label n) : ℝ :=
  if boundaryPattern H B F φ then H.muRef l G φ else 0

noncomputable def anchoredWeight (l : ℕ) (G : WeldedInstance n) (H : AbsForest n)
    (B : Finset ℕ) (F : Finset (Fin H.k)) (a : Fin H.k) (φ : Fin H.k → Label n) : ℝ :=
  if F ⊆ H.Ctree φ a then sectorWeight l G H B F φ else 0

noncomputable def sectorCoefficientMap (l : ℕ) (G : WeldedInstance n) (H : AbsForest n)
    (B : Finset ℕ) (F : Finset (Fin H.k)) (v : Fin H.k) :
    (FixedDataFunctions.Data H → ℂ) →ₗ[ℂ] Hil (Fin H.k → Label n) :=
  ((eventSpace (fun φ => F ⊆ H.Ctree φ v)).starProjection.toLinearMap).comp
    (coefficientMap (sectorWeight l G H B F) (fun φ => H.Wfix φ v))

noncomputable def sectorSpace (l : ℕ) (G : WeldedInstance n) (H : AbsForest n)
    (B : Finset ℕ) (F : Finset (Fin H.k)) : Submodule ℂ (Hil (Fin H.k → Label n)) :=
  ⨆ v, LinearMap.range (sectorCoefficientMap l G H B F v)

lemma root_condition_iff (H : AbsForest n) (F : Finset (Fin H.k))
    (a : Fin H.k) (ha : a ∈ F) (v : Fin H.k) (φ : Fin H.k → Label n) :
    F ⊆ H.Ctree φ v ↔ F ⊆ H.Ctree φ a ∧ v ∈ H.Ctree φ a := by
  constructor
  · intro hF
    have hav := hF ha
    exact ⟨by simpa only [ctree_eq_of_mem H φ a v hav] using hF,
      (ctree_mem_symm H φ a v).mp hav⟩
  · rintro ⟨hF, hv⟩
    simpa only [ctree_eq_of_mem H φ v a hv] using hF

lemma sector_generator_eq (H : AbsForest n) (B : Finset ℕ) (F : Finset (Fin H.k))
    (a : Fin H.k) (ha : a ∈ F) (v : Fin H.k) (h : FixedDataFunctions.Data H → ℂ) :
    sectorCoefficientMap l G H B F v h =
      lift (anchoredWeight l G H B F a)
        ((fun d : FixedDataFunctions.Data H => if v ∈ d.1 then h d else 0) ∘
          (fun φ => H.Wfix φ a)) := by
  change (eventSpace (fun φ => F ⊆ H.Ctree φ v)).starProjection
    (lift (sectorWeight l G H B F) (h ∘ (fun φ => H.Wfix φ v))) = _
  rw [eventSpace_projection]
  ext φ
  simp only [diagProj_apply]
  change (if F ⊆ H.Ctree φ v then
      (Real.sqrt (sectorWeight l G H B F φ) : ℂ) * h (H.Wfix φ v) else 0) =
    (Real.sqrt (anchoredWeight l G H B F a φ) : ℂ) *
      (if v ∈ H.Ctree φ a then h (H.Wfix φ a) else 0)
  by_cases hA : F ⊆ H.Ctree φ a
  · by_cases hv : v ∈ H.Ctree φ a
    · have hV := (root_condition_iff H F a ha v φ).mpr ⟨hA, hv⟩
      have hw := wfix_eq_of_mem H φ a v (hV ha)
      simp only [if_pos hV, if_pos hv, anchoredWeight, if_pos hA, hw]
    · have hV : ¬F ⊆ H.Ctree φ v := fun hV => hv ((root_condition_iff H F a ha v φ).mp hV).2
      simp only [if_neg hV, if_neg hv, mul_zero]
  · have hV : ¬F ⊆ H.Ctree φ v := fun hV => hA ((root_condition_iff H F a ha v φ).mp hV).1
    simp only [if_neg hV, anchoredWeight, if_neg hA, Real.sqrt_zero,
      Complex.ofReal_zero, zero_mul]

lemma anchor_generator_eq (H : AbsForest n) (B : Finset ℕ) (F : Finset (Fin H.k))
    (a : Fin H.k) (h : FixedDataFunctions.Data H → ℂ) :
    sectorCoefficientMap l G H B F a h =
      lift (anchoredWeight l G H B F a) (h ∘ (fun φ => H.Wfix φ a)) := by
  change (eventSpace (fun φ => F ⊆ H.Ctree φ a)).starProjection
    (lift (sectorWeight l G H B F) (h ∘ (fun φ => H.Wfix φ a))) = _
  rw [eventSpace_projection]
  ext φ
  simp only [diagProj_apply]
  change (if F ⊆ H.Ctree φ a then
      (Real.sqrt (sectorWeight l G H B F φ) : ℂ) * h (H.Wfix φ a) else 0) =
    (Real.sqrt (anchoredWeight l G H B F a φ) : ℂ) * h (H.Wfix φ a)
  by_cases hA : F ⊆ H.Ctree φ a <;>
    simp only [anchoredWeight, hA, if_true, if_false, Real.sqrt_zero,
      Complex.ofReal_zero, zero_mul]

/-- A nonempty boundary pattern selects one tree component, so its full
coefficient space is one fixed-data space at any anchor in the pattern. -/
theorem sectorSpace_eq_dataSpace (H : AbsForest n) (B : Finset ℕ)
    (F : Finset (Fin H.k)) (a : Fin H.k) (ha : a ∈ F) :
    sectorSpace l G H B F =
      dataSpace (anchoredWeight l G H B F a) (fun φ => H.Wfix φ a) := by
  apply le_antisymm
  · apply iSup_le
    intro v f hf
    obtain ⟨h, rfl⟩ := hf
    rw [sector_generator_eq H B F a ha v h]
    exact lift_mem_dataSpace _ _ _
  · intro f hf
    obtain ⟨h, rfl⟩ := (mem_dataSpace _ _ f).mp hf
    apply (le_iSup (fun v : Fin H.k => LinearMap.range (sectorCoefficientMap l G H B F v)) a)
    exact ⟨h, anchor_generator_eq H B F a h⟩

lemma anchoredWeight_nonneg (H : AbsForest n) (hH : H.IsValid) (B : Finset ℕ)
    (F : Finset (Fin H.k)) (a : Fin H.k) (φ : Fin H.k → Label n) :
    0 ≤ anchoredWeight l G H B F a φ := by
  unfold anchoredWeight sectorWeight
  split_ifs
  · exact ForestFactorization.muRef_nonneg l G H hH φ
  · exact le_refl (0 : ℝ)
  · exact le_refl (0 : ℝ)

lemma pattern_iff_avoid_of_wfix (H : AbsForest n) (hH : H.IsValid)
    (B : Finset ℕ) (F : Finset (Fin H.k)) (a : Fin H.k)
    (hs : ∀ u, H.graph.Reachable a u) (φ φ₀ : Fin H.k → Label n)
    (hpat : boundaryPattern H B F φ₀) (hF : F ⊆ H.Ctree φ₀ a)
    (hw : H.Wfix φ a = H.Wfix φ₀ a) :
    boundaryPattern H B F φ ↔
      ∀ u, H.graph.Reachable a u → u ∉ H.Ctree φ a → (φ u).val ∉ B := by
  have hC : H.Ctree φ a = H.Ctree φ₀ a := congrArg Prod.fst hw
  have hagree := (wfix_eq_iff_agree_sfix H hH φ φ₀ a).mp hw
  constructor
  · intro hp u _ hu hB
    exact hu (hC.symm ▸ hF ((hp u).mp hB))
  · intro hav u
    by_cases hu : u ∈ H.Ctree φ₀ a
    · rw [hagree u (ctree_subset_sfix H φ₀ a hu)]
      exact hpat u
    · have hf : u ∉ F := fun hf => hu (hF hf)
      have hb := hav u (hs u) (fun hx => hu (hC ▸ hx))
      exact ⟨fun h => (hb h).elim, fun h => (hf h).elim⟩

/-- On a supported fixed-data fiber the exact boundary-pattern sector is
the canonical fixed-data and boundary-avoidance source law. -/
theorem fiber_weight_eq_source (H : AbsForest n) (hH : H.IsValid)
    (B : Finset ℕ) (F : Finset (Fin H.k)) (a : Fin H.k)
    (hs : ∀ u, H.graph.Reachable a u) (φ₀ : Fin H.k → Label n)
    (hpat : boundaryPattern H B F φ₀) (hF : F ⊆ H.Ctree φ₀ a)
    (φ : Fin H.k → Label n) :
    (if H.Wfix φ a = H.Wfix φ₀ a then anchoredWeight l G H B F a φ else 0) =
      sourceWeight l G H φ₀ a B φ := by
  by_cases hw : H.Wfix φ a = H.Wfix φ₀ a
  · have hC : H.Ctree φ a = H.Ctree φ₀ a := congrArg Prod.fst hw
    have hA : F ⊆ H.Ctree φ a := hC.symm ▸ hF
    have hi := pattern_iff_avoid_of_wfix H hH B F a hs φ φ₀ hpat hF hw
    rw [if_pos hw]
    unfold anchoredWeight sectorWeight sourceWeight
    rw [if_pos hA]
    by_cases hp : boundaryPattern H B F φ
    · exact (if_pos hp).trans (if_pos ⟨hw, hi.mp hp⟩).symm
    · exact (if_neg hp).trans (if_neg (fun h => hp (hi.mpr h.2))).symm
  · simp only [hw, if_false, sourceWeight, false_and]

theorem anchored_weight_witness (H : AbsForest n) (hH : H.IsValid)
    (B : Finset ℕ) (F : Finset (Fin H.k)) (a : Fin H.k)
    (hs : ∀ u, H.graph.Reachable a u) (φ₀ : Fin H.k → Label n)
    (hpos : 0 < anchoredWeight l G H B F a φ₀) :
    H.muRef l G φ₀ ≠ 0 ∧ ∀ φ,
      (if H.Wfix φ a = H.Wfix φ₀ a then anchoredWeight l G H B F a φ else 0) =
        sourceWeight l G H φ₀ a B φ := by
  have hF : F ⊆ H.Ctree φ₀ a := by
    by_contra hh
    simp only [anchoredWeight, if_neg hh] at hpos
    exact (lt_irrefl 0) hpos
  have hpat : boundaryPattern H B F φ₀ := by
    by_contra hh
    simp only [anchoredWeight, if_pos hF, sectorWeight, if_neg hh] at hpos
    exact (lt_irrefl 0) hpos
  have href : 0 < H.muRef l G φ₀ := by
    simpa only [anchoredWeight, if_pos hF, sectorWeight, if_pos hpat] using hpos
  exact ⟨ne_of_gt href, fiber_weight_eq_source H hH B F a hs φ₀ hpat hF⟩

theorem sector_stable_representative (H : AbsForest n) (hH : H.IsValid)
    (B : Finset ℕ) (F : Finset (Fin H.k)) (a : Fin H.k) (ha : a ∈ F)
    (hs : ∀ u, H.graph.Reachable a u)
    (hG : G.IsValid) (hn : 16 ≤ n) (hl : 2 ≤ l) (hln : l ≤ n - 4)
    (hB : Vbd n l ⊆ B) (hBw : Disjoint B (Vweld n))
    (hsurvive : (H.k : ℝ) * (B.card : ℝ) * (4 / (2 : ℝ) ^ n) ≤ 1 / 2)
    (hsmall : (H.k : ℝ) ^ 2 * (96 * ((n : ℝ) + 1) / (2 : ℝ) ^ n) ≤ 1 / 2)
    (f₀ : Hil (Fin H.k → Label n)) (hf₀ : f₀ ∈ sectorSpace l G H B F) :
    ∃! f : Hil (Fin H.k → Label n),
      f ∈ sectorSpace l G H B F ∧
      f ∈ (sectorSpace l G H B F ⊓ (eventSpace Function.Injective)ᗮ)ᗮ ∧
      (eventSpace Function.Injective).starProjection f =
        (eventSpace Function.Injective).starProjection f₀ ∧
      ‖f‖ ^ 2 ≤ 2 * ‖(eventSpace Function.Injective).starProjection f₀‖ ^ 2 := by
  let μ := anchoredWeight l G H B F a
  let data : Unit → (Fin H.k → Label n) → FixedDataFunctions.Data H :=
    fun _ φ => H.Wfix φ a
  let S := sectorSpace l G H B F
  let P := fun ab : Fin H.k × Fin H.k => Collision H ab.1 ab.2
  let Q := fun (ab : Fin H.k × Fin H.k) (_ : Unit) => FixedCollision H a ab.1 ab.2
  let ε : ℝ := 96 * ((n : ℝ) + 1) / (2 : ℝ) ^ n
  have hμ : ∀ φ, 0 ≤ μ φ := anchoredWeight_nonneg H hH B F a
  have hS : S = dataSpace μ (data ()) := sectorSpace_eq_dataSpace H B F a ha
  have hfixed : ∀ (ab : Fin H.k × Fin H.k) (i : Unit) f,
      f ∈ dataSpace μ (data i) →
      (eventSpace (Q ab i)).starProjection f ∈ S ⊓ (eventSpace Function.Injective)ᗮ := by
    intro ab i f hf
    refine ⟨?_, (fixed_mask_mem_kernel H hH μ a ab.1 ab.2 f hf).2⟩
    rw [hS]
    exact fixed_mask_mem_local H hH μ a ab.1 ab.2 f hf
  have hcap : ∀ (ab : Fin H.k × Fin H.k) (i : Unit) d,
      (∑ φ, if data i φ = d ∧ (P ab φ ∧ ¬Q ab i φ) then μ φ else 0) ≤
        ε * ∑ φ, if data i φ = d then μ φ else 0 := by
    intro ab i d
    have hbnd := SourceFiberBound.free_collision_fiber_bound H hH μ hμ a hs
      hG hn hl hln B hB hBw hsurvive (anchored_weight_witness H hH B F a hs)
      ab.1 ab.2 d
    have he (φ : Fin H.k → Label n) :
        (data i φ = d ∧ (P ab φ ∧ ¬Q ab i φ)) ↔
          (H.Wfix φ a = d ∧ FreeCollision H a ab.1 ab.2 φ) := by
      dsimp only [data, P, Q]
      unfold FixedCollision FreeCollision
      tauto
    calc
      _ = ∑ φ, if H.Wfix φ a = d ∧ FreeCollision H a ab.1 ab.2 φ then μ φ else 0 := by
        apply Finset.sum_congr rfl
        intro φ _
        by_cases hh : data i φ = d ∧ (P ab φ ∧ ¬Q ab i φ)
        · exact (if_pos hh).trans (if_pos ((he φ).mp hh)).symm
        · exact (if_neg hh).trans (if_neg (mt (he φ).mpr hh)).symm
      _ ≤ _ := hbnd
  have hdecomp : ∀ f ∈ S, f ∈ (S ⊓ (eventSpace Function.Injective)ᗮ)ᗮ →
      ∃ v : Unit → Hil (Fin H.k → Label n),
        (∀ i, v i ∈ dataSpace μ (data i)) ∧
        f = ∑ i, v i ∧ (∑ i, ‖v i‖ ^ 2) ≤ ‖f‖ ^ 2 := by
    intro f hf _
    refine ⟨fun _ => f, fun _ => ?_, by simp, by simp⟩
    exact hS ▸ hf
  have hsmall' : (Fintype.card (Fin H.k × Fin H.k) : ℝ) *
      (Fintype.card Unit : ℝ) * ε ≤ 1 / 2 := by
    calc
      _ = (H.k : ℝ) ^ 2 * ε := by
        simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_unique,
          Nat.cast_mul, Nat.cast_one, mul_one]
        ring
      _ ≤ _ := hsmall
  exact CollisionStability.stable_representative_of_fiber_bounds μ hμ data S
    Function.Injective P Q (not_injective_iff_collision H) (fun _ _ _ h => h.1)
    hfixed ε (by positivity) hcap hdecomp hsmall' f₀ hf₀

end WeldedPath.Supplement.BoundarySector

end

-- Solutions.WeightedForestCentering
section

namespace FiniteWeightedForest

open scoped BigOperators
open Classical

/-- Conditional centering on one side of a separator gives orthogonality to
all functions of the other side, even before fixing the opposite endpoint.
The coupling factor may be any function of the two sides. -/
theorem weighted_bridge_centered_sum {Ω A B R : Type*}
    [Fintype Ω] [Fintype A] [Fintype B] [CommSemiring R]
    (e : Ω ≃ A × B) (f u : A → R) (g v : B → R) (K : A → B → R)
    (hu : ∀ b, ∑ a, f a * K a b * u a = 0) :
    (∑ ω, f (e ω).1 * g (e ω).2 * K (e ω).1 (e ω).2 *
      (u (e ω).1 * v (e ω).2)) = 0 := by
  rw [Fintype.sum_equiv e _ (fun p => f p.1 * g p.2 * K p.1 p.2 * (u p.1 * v p.2))
    (fun _ => rfl), Fintype.sum_prod_type, Finset.sum_comm]
  calc
    _ = ∑ b, (g b * v b) * (∑ a, f a * K a b * u a) := by
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = 0 := by simp only [hu, mul_zero, Finset.sum_const_zero]

/-- Fiberwise centering permits the residual to depend on the outside data,
and the comparison function to depend on the shared inside endpoint. -/
theorem weighted_bridge_fiber_centered_sum {Ω A B D R : Type*}
    [Fintype Ω] [Fintype A] [Fintype B] [Fintype D] [CommSemiring R]
    (e : Ω ≃ A × B) (f : A → R) (g : B → R) (K u : A → B → R)
    (data : A → D) (v : D → B → R)
    (hu : ∀ b d, (∑ a, if data a = d then f a * K a b * u a b else 0) = 0) :
    (∑ ω, f (e ω).1 * g (e ω).2 * K (e ω).1 (e ω).2 *
      (u (e ω).1 (e ω).2 * v (data (e ω).1) (e ω).2)) = 0 := by
  classical
  rw [Fintype.sum_equiv e _ (fun p => f p.1 * g p.2 * K p.1 p.2 *
    (u p.1 p.2 * v (data p.1) p.2)) (fun _ => rfl),
    Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro b _
  calc
    _ = g b * ∑ a, (f a * K a b * u a b) * v (data a) b := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = g b * ∑ d, (∑ a, if data a = d then f a * K a b * u a b else 0) * v d b := by
      congr 1
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      simp
    _ = 0 := by simp only [hu, zero_mul, Finset.sum_const_zero, mul_zero]

/-- Specialization to a real weighted forest and complex coefficient
functions. Local vertex restrictions remain part of the branch weights. -/
theorem forestWeight_centered_bridge_sum {V X : Type*} [Fintype V] [DecidableEq V]
    [Fintype X] [Zero X] (E : Finset (V × V)) (P : V → Prop) [DecidablePred P]
    (K : (V × V) → X → X → ℝ) (allowed : V → X → Prop)
    (e : V × V) (he : e ∈ E) (hleft : P e.1) (hright : ¬P e.2)
    (hclosed : ∀ p ∈ E.erase e, P p.1 ↔ P p.2)
    (u : ({v // P v} → X) → ℂ) (v : ({v // ¬P v} → X) → ℂ)
    (hu : ∀ x : X,
      ∑ a : {v // P v} → X,
        (supportedBranchWeight (E.erase e) P K allowed a : ℂ) *
        (K e (a ⟨e.1, hleft⟩) x : ℂ) * u a = 0) :
    (∑ φ : V → X, (forestWeight E K allowed φ : ℂ) *
      (u (fun a => φ a) * v (fun b => φ b))) = 0 := by
  let split : (V → X) ≃ (({v // P v} → X) × ({v // ¬P v} → X)) :=
    Equiv.piEquivPiSubtypeProd P (fun _ => X)
  have hfactor (φ : V → X) := forestWeight_bridge_branches E P K allowed φ e he hclosed
  simp_rw [hfactor, Complex.ofReal_mul]
  exact weighted_bridge_centered_sum split
    (fun a => (supportedBranchWeight (E.erase e) P K allowed a : ℂ)) u
    (fun b => (supportedBranchWeight (E.erase e) (fun v => ¬P v) K allowed b : ℂ)) v
    (fun a b => (K e (a ⟨e.1, hleft⟩) (b ⟨e.2, hright⟩) : ℂ))
    (fun b => hu (b ⟨e.2, hright⟩))

/-- The two-endpoint conditional version needed when both local coefficient
spaces can see the labels of the separating edge. -/
theorem forestWeight_fiber_centered_bridge_sum {V X : Type*} [Fintype V] [DecidableEq V]
    [Fintype X] [Zero X] (E : Finset (V × V)) (P : V → Prop) [DecidablePred P]
    (K : (V × V) → X → X → ℝ) (allowed : V → X → Prop)
    (e : V × V) (he : e ∈ E) (hleft : P e.1) (hright : ¬P e.2)
    (hclosed : ∀ p ∈ E.erase e, P p.1 ↔ P p.2)
    (u : X → ({v // P v} → X) → ℂ) (v : X → ({v // ¬P v} → X) → ℂ)
    (hu : ∀ x y : X,
      (∑ a : {v // P v} → X,
        if a ⟨e.1, hleft⟩ = y then
          (supportedBranchWeight (E.erase e) P K allowed a : ℂ) *
          (K e (a ⟨e.1, hleft⟩) x : ℂ) * u x a else 0) = 0) :
    (∑ φ : V → X, (forestWeight E K allowed φ : ℂ) *
      (u (φ e.2) (fun a => φ a) * v (φ e.1) (fun b => φ b))) = 0 := by
  classical
  let split : (V → X) ≃ (({v // P v} → X) × ({v // ¬P v} → X)) :=
    Equiv.piEquivPiSubtypeProd P (fun _ => X)
  have hfactor (φ : V → X) := forestWeight_bridge_branches E P K allowed φ e he hclosed
  simp_rw [hfactor, Complex.ofReal_mul]
  exact weighted_bridge_fiber_centered_sum split
    (fun a => (supportedBranchWeight (E.erase e) P K allowed a : ℂ))
    (fun b => (supportedBranchWeight (E.erase e) (fun v => ¬P v) K allowed b : ℂ))
    (fun a b => (K e (a ⟨e.1, hleft⟩) (b ⟨e.2, hright⟩) : ℂ))
    (fun a b => u (b ⟨e.2, hright⟩) a) (fun a => a ⟨e.1, hleft⟩) v
    (fun b y => hu (b ⟨e.2, hright⟩) y)

end FiniteWeightedForest

end

-- Solutions.WeldedPathForestCentering
section

namespace WeldedPath.Supplement.ForestFactorization

open scoped BigOperators
open FiniteWeightedForest
open Classical

variable {n : ℕ}

def forestEdgeCut (H : AbsForest n) (e : Fin H.k × Fin H.k) (u : Fin H.k) : Prop :=
  (edgeGraph (H.E.erase e)).Reachable e.1 u

theorem forestEdgeCut_spec (H : AbsForest n) (hH : H.IsValid)
    (e : Fin H.k × Fin H.k) (he : e ∈ H.E) :
    forestEdgeCut H e e.1 ∧ ¬forestEdgeCut H e e.2 ∧
      ∀ p ∈ H.E.erase e, forestEdgeCut H e p.1 ↔ forestEdgeCut H e p.2 := by
  refine ⟨SimpleGraph.Reachable.refl _, ?_, ?_⟩
  · exact forest_cut_not_reachable H.E e hH.1 hH.2.1 he
  · exact forest_cut_closed H.E e hH.1

/-- The Markov orthogonality identity for the actual reference measure.
Conditional centering of a subtree at its single connecting endpoint makes
it orthogonal to every function of the coordinates outside the subtree. -/
theorem muRef_centered_bridge_sum (l : ℕ) (G : WeldedInstance n) (H : AbsForest n)
    (hH : H.IsValid) (P : Fin H.k → Prop) [DecidablePred P]
    (e : Fin H.k × Fin H.k) (he : e ∈ H.E) (hleft : P e.1) (hright : ¬P e.2)
    (hclosed : ∀ p ∈ H.E.erase e, P p.1 ↔ P p.2)
    (u : ({v // P v} → Label n) → ℂ) (v : ({v // ¬P v} → Label n) → ℂ)
    (hu : ∀ x : Label n,
      ∑ a : {v // P v} → Label n,
        (supportedBranchWeight (H.E.erase e) P (componentKernel l G H)
          (referenceAllowed l H) a : ℂ) *
        (kappa l G (H.color e) (a ⟨e.1, hleft⟩).val x.val : ℂ) * u a = 0) :
    (∑ φ : Fin H.k → Label n, (H.muRef l G φ : ℂ) *
      (u (fun a => φ a) * v (fun b => φ b))) = 0 := by
  have hcenter := forestWeight_centered_bridge_sum H.E P (componentKernel l G H)
    (referenceAllowed l H) e he hleft hright hclosed u v hu
  simp_rw [muRef_eq_scale_forestWeight l G H hH, Complex.ofReal_mul, mul_assoc]
  rw [← Finset.mul_sum]
  rw [hcenter, mul_zero]

/-- The precise Markov orthogonality form for local fixed-data coefficient
spaces: the residual may see the opposite endpoint, and the earlier
coefficient may see the shared endpoint on the residual's side. Centering
is required separately for both endpoint labels. -/
theorem muRef_fiber_centered_bridge_sum (l : ℕ) (G : WeldedInstance n) (H : AbsForest n)
    (hH : H.IsValid) (P : Fin H.k → Prop) [DecidablePred P]
    (e : Fin H.k × Fin H.k) (he : e ∈ H.E) (hleft : P e.1) (hright : ¬P e.2)
    (hclosed : ∀ p ∈ H.E.erase e, P p.1 ↔ P p.2)
    (u : Label n → ({v // P v} → Label n) → ℂ)
    (v : Label n → ({v // ¬P v} → Label n) → ℂ)
    (hu : ∀ x y : Label n,
      (∑ a : {v // P v} → Label n,
        if a ⟨e.1, hleft⟩ = y then
          (supportedBranchWeight (H.E.erase e) P (componentKernel l G H)
            (referenceAllowed l H) a : ℂ) *
          (kappa l G (H.color e) (a ⟨e.1, hleft⟩).val x.val : ℂ) * u x a else 0) = 0) :
    (∑ φ : Fin H.k → Label n, (H.muRef l G φ : ℂ) *
      (u (φ e.2) (fun a => φ a) * v (φ e.1) (fun b => φ b))) = 0 := by
  have hcenter := forestWeight_fiber_centered_bridge_sum H.E P (componentKernel l G H)
    (referenceAllowed l H) e he hleft hright hclosed u v (by
      intro x y
      convert hu x y using 1
      apply Finset.sum_congr rfl
      intro a _
      split_ifs <;> rfl)
  simp_rw [muRef_eq_scale_forestWeight l G H hH, Complex.ofReal_mul, mul_assoc]
  rw [← Finset.mul_sum]
  rw [hcenter, mul_zero]

/-- Symmetric stored-edge orientation of the preceding theorem. -/
theorem muRef_fiber_centered_bridge_sum_right
    (l : ℕ) (G : WeldedInstance n) (H : AbsForest n)
    (hH : H.IsValid) (P : Fin H.k → Prop) [DecidablePred P]
    (e : Fin H.k × Fin H.k) (he : e ∈ H.E) (hleft : P e.1) (hright : ¬P e.2)
    (hclosed : ∀ p ∈ H.E.erase e, P p.1 ↔ P p.2)
    (u : Label n → ({v // ¬P v} → Label n) → ℂ)
    (v : Label n → ({v // P v} → Label n) → ℂ)
    (hu : ∀ x y : Label n,
      (∑ b : {v // ¬P v} → Label n,
        if b ⟨e.2, hright⟩ = y then
          (supportedBranchWeight (H.E.erase e) (fun v => ¬P v) (componentKernel l G H)
            (referenceAllowed l H) b : ℂ) *
          (kappa l G (H.color e) x.val (b ⟨e.2, hright⟩).val : ℂ) * u x b else 0) = 0) :
    (∑ φ : Fin H.k → Label n, (H.muRef l G φ : ℂ) *
      (u (φ e.1) (fun b => φ b) * v (φ e.2) (fun a => φ a))) = 0 := by
  let split : (Fin H.k → Label n) ≃
      (({v // ¬P v} → Label n) × ({v // P v} → Label n)) :=
    (Equiv.piEquivPiSubtypeProd P (fun _ => Label n)).trans (Equiv.prodComm _ _)
  let L := supportedBranchWeight (H.E.erase e) P (componentKernel l G H) (referenceAllowed l H)
  let R := supportedBranchWeight (H.E.erase e) (fun v => ¬P v)
    (componentKernel l G H) (referenceAllowed l H)
  have hz : (∑ φ : Fin H.k → Label n,
      (R (fun b => φ b) : ℂ) * (L (fun a => φ a) : ℂ) *
        (kappa l G (H.color e) (φ e.1).val (φ e.2).val : ℂ) *
        (u (φ e.1) (fun b => φ b) * v (φ e.2) (fun a => φ a))) = 0 :=
    weighted_bridge_fiber_centered_sum split (fun b => (R b : ℂ)) (fun a => (L a : ℂ))
      (fun b a => (kappa l G (H.color e) (a ⟨e.1, hleft⟩).val (b ⟨e.2, hright⟩).val : ℂ))
      (fun b a => u (a ⟨e.1, hleft⟩) b) (fun b => b ⟨e.2, hright⟩) v
      (by
        intro a y
        convert hu (a ⟨e.1, hleft⟩) y using 1
        apply Finset.sum_congr rfl
        intro b _
        split_ifs <;> rfl)
  calc
    _ = (referenceScale l G H : ℂ) * (∑ φ : Fin H.k → Label n,
      (R (fun b => φ b) : ℂ) * (L (fun a => φ a) : ℂ) *
        (kappa l G (H.color e) (φ e.1).val (φ e.2).val : ℂ) *
        (u (φ e.1) (fun b => φ b) * v (φ e.2) (fun a => φ a))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro φ _
      rw [muRef_eq_scale_forestWeight l G H hH φ,
        forestWeight_bridge_branches H.E P (componentKernel l G H) (referenceAllowed l H)
          φ e he hclosed]
      simp only [Complex.ofReal_mul, componentKernel]
      change (_ * ((L _ : ℂ) * (R _ : ℂ) * _)) * _ = _
      ring
    _ = 0 := by rw [hz, mul_zero]

/-- The same identity after arbitrary extra local vertex restrictions. This
includes fixed-data/boundary conditions, after `descriptionWeight_eq_forestWeight`. -/
theorem supported_reference_centered_bridge_sum
    (l : ℕ) (G : WeldedInstance n) (H : AbsForest n)
    (allowed : Fin H.k → Label n → Prop) (P : Fin H.k → Prop) [DecidablePred P]
    (e : Fin H.k × Fin H.k) (he : e ∈ H.E) (hleft : P e.1) (hright : ¬P e.2)
    (hclosed : ∀ p ∈ H.E.erase e, P p.1 ↔ P p.2)
    (u : ({v // P v} → Label n) → ℂ) (v : ({v // ¬P v} → Label n) → ℂ)
    (hu : ∀ x : Label n,
      ∑ a : {v // P v} → Label n,
        (supportedBranchWeight (H.E.erase e) P (componentKernel l G H) allowed a : ℂ) *
        (kappa l G (H.color e) (a ⟨e.1, hleft⟩).val x.val : ℂ) * u a = 0) :
    (∑ φ : Fin H.k → Label n,
      (forestWeight H.E (componentKernel l G H) allowed φ : ℂ) *
      (u (fun a => φ a) * v (fun b => φ b))) = 0 :=
  forestWeight_centered_bridge_sum H.E P (componentKernel l G H)
    allowed e he hleft hright hclosed u v hu

end WeldedPath.Supplement.ForestFactorization

end

-- Solutions.WeldedPathEdgeCoefficientSplit
section

namespace WeldedPath.Supplement.EdgeCoefficientSplit

open scoped BigOperators
open Classical FiniteWeightedForest ForestFactorization FixedDataFunctions
open WeldedPath.WeightedCoefficients

variable {n : ℕ}

def WeldPair (x y : Label n) : Prop := x.val ∈ Vweld n ∧ y.val ∈ Vweld n

lemma weld_iff (H : AbsForest n) (e : Fin H.k × Fin H.k) (c p : Fin H.k)
    (hends : e = (c, p) ∨ e = (p, c)) (φ : Fin H.k → Label n) :
    H.IsWeldUnder φ e ↔ WeldPair (φ c) (φ p) := by
  rcases hends with rfl | rfl
  · rfl
  · exact and_comm

lemma endpoint_pairs_factor (H : AbsForest n) (hH : H.IsValid)
    (e : Fin H.k × Fin H.k) (he : e ∈ H.E) (c p : Fin H.k)
    (hends : e = (c, p) ∨ e = (p, c)) :
    Function.FactorsThrough (fun φ : Fin H.k → Label n => (φ c, φ p))
      (fun φ => H.Wfix φ c) ∧
    Function.FactorsThrough (fun φ : Fin H.k → Label n => (φ c, φ p))
      (fun φ => H.Wfix φ p) := by
  rcases hends with rfl | rfl
  · exact ⟨endpoint_pair_factors_left H hH _ he, endpoint_pair_factors_right H hH _ he⟩
  · exact ⟨(endpoint_pair_factors_right H hH _ he).comp_left Prod.swap,
      (endpoint_pair_factors_left H hH _ he).comp_left Prod.swap⟩

lemma nonweld_data_eq (H : AbsForest n) (hH : H.IsValid)
    (e : Fin H.k × Fin H.k) (he : e ∈ H.E) (c p : Fin H.k)
    (hends : e = (c, p) ∨ e = (p, c)) (φ : Fin H.k → Label n)
    (hw : ¬H.IsWeldUnder φ e) : H.Wfix φ c = H.Wfix φ p := by
  rcases hends with rfl | rfl
  · exact wfix_eq_on_nonweld_edge H hH _ he φ hw
  · exact (wfix_eq_on_nonweld_edge H hH _ he φ hw).symm

/-- An orientation-independent local representation on the weld event. -/
lemma weld_local_representation (H : AbsForest n) (hH : H.IsValid)
    (e : Fin H.k × Fin H.k) (c p : Fin H.k)
    (hends : e = (c, p) ∨ e = (p, c)) (P : Fin H.k → Prop)
    (hc : P c) (hcut : ∀ q ∈ H.E, q ≠ e → (P q.1 ↔ P q.2))
    (v : Fin H.k) (hv : P v) (h : Data H → ℂ) :
    ∃ f : Label n → ({a // P a} → Label n) → ℂ,
      ∀ φ : Fin H.k → Label n,
        (if H.IsWeldUnder φ e then h (H.Wfix φ v) else 0) =
          f (φ p) (fun a => φ a) := by
  have hf : Function.FactorsThrough
      (fun φ : Fin H.k → Label n => if H.IsWeldUnder φ e then h (H.Wfix φ v) else 0)
      (fun φ => (φ p, fun a : {a // P a} => φ a)) := by
    intro φ ψ hd
    dsimp only at hd ⊢
    have hp : φ p = ψ p := congrArg Prod.fst hd
    have hs : ∀ a, P a → φ a = ψ a := by
      intro a ha
      exact congrFun (congrArg Prod.snd hd) ⟨a, ha⟩
    have hceq := hs c hc
    have hend : φ e.1 = ψ e.1 ∧ φ e.2 = ψ e.2 := by
      rcases hends with rfl | rfl
      · exact ⟨hceq, hp⟩
      · exact ⟨hp, hceq⟩
    have hwiff : H.IsWeldUnder φ e ↔ H.IsWeldUnder ψ e := by
      simp only [AbsForest.IsWeldUnder, hend.1, hend.2]
    by_cases hw : H.IsWeldUnder φ e
    · rw [if_pos hw, if_pos (hwiff.mp hw)]
      apply congrArg h
      apply FixedDataSeparator.wfix_depends_on_side H φ e P hH hcut hw v hv ψ
      intro a ha
      rcases ha with ha | rfl | rfl
      · exact hs a ha
      · exact hend.1
      · exact hend.2
    · rw [if_neg hw, if_neg (mt hwiff.mpr hw)]
  obtain ⟨f, hf⟩ := (Function.factorsThrough_iff _).mp hf
  exact ⟨fun x a => f (x, a), fun φ => congrFun hf φ⟩

noncomputable def maskedReference (l : ℕ) (G : WeldedInstance n) (H : AbsForest n)
    (allowed : Fin H.k → Label n → Prop) (φ : Fin H.k → Label n) : ℝ :=
  if ∀ u, allowed u (φ u) then H.muRef l G φ else 0

lemma maskedReference_nonneg (l : ℕ) (G : WeldedInstance n) (H : AbsForest n)
    (hH : H.IsValid) (allowed : Fin H.k → Label n → Prop) (φ : Fin H.k → Label n) :
    0 ≤ maskedReference l G H allowed φ := by
  unfold maskedReference
  split_ifs
  · exact muRef_nonneg l G H hH φ
  · rfl

lemma maskedReference_eq (l : ℕ) (G : WeldedInstance n) (H : AbsForest n)
    (hH : H.IsValid) (allowed : Fin H.k → Label n → Prop) (φ : Fin H.k → Label n) :
    maskedReference l G H allowed φ = referenceScale l G H *
      forestWeight H.E (componentKernel l G H)
        (fun u x => referenceAllowed l H u x ∧ allowed u x) φ := by
  unfold maskedReference
  rw [muRef_eq_scale_forestWeight l G H hH φ]
  unfold forestWeight
  simp only [forall_and, ite_and, mul_ite, mul_zero]
  split_ifs <;> rfl

lemma supportedBranch_nonneg (l : ℕ) (G : WeldedInstance n) (H : AbsForest n)
    (E : Finset (Fin H.k × Fin H.k)) (P : Fin H.k → Prop) [DecidablePred P]
    (allowed : Fin H.k → Label n → Prop) (a : {u // P u} → Label n) :
    0 ≤ supportedBranchWeight E P (componentKernel l G H) allowed a := by
  unfold supportedBranchWeight
  split_ifs
  · exact component_edgeWeight_nonneg l G H _ _
  · rfl

/-- A child-local coefficient splits into a centered child-local residual
and a parent-local coefficient. The residual is supported on the weld event
and is orthogonal to every local coefficient on the opposite side. Local
vertex restrictions are arbitrary and may include boundary conditions. -/
theorem edge_split_measurable (l : ℕ) (G : WeldedInstance n) (hG : G.IsValid)
    (H : AbsForest n) (hH : H.IsValid) (allowed : Fin H.k → Label n → Prop)
    (e : Fin H.k × Fin H.k) (he : e ∈ H.E) (c p : Fin H.k)
    (hends : e = (c, p) ∨ e = (p, c)) (P : Fin H.k → Prop) [DecidablePred P]
    (hc : P c) (hp : ¬P p)
    (hcut : ∀ q ∈ H.E, q ≠ e → (P q.1 ↔ P q.2)) (h : Data H → ℂ) :
    ∃ r t : Data H → ℂ,
      (∀ φ : Fin H.k → Label n,
        h (H.Wfix φ c) = r (H.Wfix φ c) + t (H.Wfix φ p)) ∧
      (∀ φ : Fin H.k → Label n, ¬H.IsWeldUnder φ e → r (H.Wfix φ c) = 0) ∧
      (∀ k : (Fin H.k → Label n) → ℂ,
        Function.FactorsThrough
          (fun φ => if H.IsWeldUnder φ e then k φ else 0)
          (fun φ => (φ c, fun b : {b // ¬P b} => φ b)) →
        inner ℂ
          (lift (maskedReference l G H allowed) k)
          (lift (maskedReference l G H allowed) (fun φ => r (H.Wfix φ c))) = 0) := by
  let A := {a : Fin H.k // P a} → Label n
  let B := {a : Fin H.k // ¬P a} → Label n
  let ca : {a // P a} := ⟨c, hc⟩
  let pb : {a // ¬P a} := ⟨p, hp⟩
  let support := fun u x => referenceAllowed l H u x ∧ allowed u x
  let L : A → ℝ := supportedBranchWeight (H.E.erase e) P (componentKernel l G H) support
  let R : B → ℝ := supportedBranchWeight (H.E.erase e) (fun u => ¬P u)
    (componentKernel l G H) support
  obtain ⟨f, hf⟩ := weld_local_representation H hH e c p hends P hc hcut c hc h
  let w : Label n → A → ℝ := fun x a => L a * kappa l G (H.color e) (a ca).val x.val
  have hw : ∀ x a, 0 ≤ w x a := by
    intro x a
    exact mul_nonneg (supportedBranch_nonneg l G H _ P support a)
      (KappaKernel.kappa_nonneg l G (H.color e) (a ca).val x.val)
  let mean : Label n → Label n → ℂ := fun x y =>
    conditionalMean (w x) (fun a => a ca) (f x) y
  let residual : (Fin H.k → Label n) → ℂ := fun φ =>
    if H.IsWeldUnder φ e then h (H.Wfix φ c) - mean (φ p) (φ c) else 0
  let transfer : (Fin H.k → Label n) → ℂ := fun φ =>
    if H.IsWeldUnder φ e then mean (φ p) (φ c) else h (H.Wfix φ p)
  have hpairs := endpoint_pairs_factor H hH e he c p hends
  have hres : Function.FactorsThrough residual (fun φ => H.Wfix φ c) := by
    intro φ ψ hd
    have hval := hpairs.1 hd
    have hcval : φ c = ψ c := congrArg Prod.fst hval
    have hpval : φ p = ψ p := congrArg Prod.snd hval
    have hweq : H.IsWeldUnder φ e ↔ H.IsWeldUnder ψ e := by
      rw [weld_iff H e c p hends φ, weld_iff H e c p hends ψ, hcval, hpval]
    dsimp only [residual]
    simp only [hweq, hd, hcval, hpval]
  have htrans : Function.FactorsThrough transfer (fun φ => H.Wfix φ p) := by
    intro φ ψ hd
    have hval := hpairs.2 hd
    have hcval : φ c = ψ c := congrArg Prod.fst hval
    have hpval : φ p = ψ p := congrArg Prod.snd hval
    have hweq : H.IsWeldUnder φ e ↔ H.IsWeldUnder ψ e := by
      rw [weld_iff H e c p hends φ, weld_iff H e c p hends ψ, hcval, hpval]
    dsimp only [transfer]
    simp only [hweq, hd, hcval, hpval]
  obtain ⟨r, hr'⟩ := (Function.factorsThrough_iff _).mp hres
  obtain ⟨t, ht'⟩ := (Function.factorsThrough_iff _).mp htrans
  have hr (φ : Fin H.k → Label n) : r (H.Wfix φ c) = residual φ := (congrFun hr' φ).symm
  have ht (φ : Fin H.k → Label n) : t (H.Wfix φ p) = transfer φ := (congrFun ht' φ).symm
  refine ⟨r, t, ?_, ?_, ?_⟩
  · intro φ
    rw [hr, ht]
    by_cases hwel : H.IsWeldUnder φ e
    · simp [residual, transfer, hwel]
    · simp [residual, transfer, hwel, nonweld_data_eq H hH e he c p hends φ hwel]
  · intro φ hwel
    simp [hr, residual, hwel]
  · intro k hk
    obtain ⟨g₀, hg₀⟩ := (Function.factorsThrough_iff _).mp hk
    let g : Label n → B → ℂ := fun y b => g₀ (y, b)
    have hg (φ : Fin H.k → Label n) :
        (if H.IsWeldUnder φ e then k φ else 0) = g (φ c) (fun b => φ b) :=
      congrFun hg₀ φ
    let centered : Label n → A → ℂ := fun x a =>
      if WeldPair (a ca) x then f x a - mean x (a ca) else 0
    have hrepr (φ : Fin H.k → Label n) :
        residual φ = centered (φ p) (fun a => φ a) := by
      have hiff := weld_iff H e c p hends φ
      dsimp only [residual, centered]
      by_cases hwel : H.IsWeldUnder φ e
      · have hfeq : h (H.Wfix φ c) = f (φ p) (fun a => φ a) := by
          simpa only [if_pos hwel] using hf φ
        simp only [hwel, hiff.mp hwel, ite_true, hfeq, ca]
      · simp only [hwel, mt hiff.mpr hwel, ite_false, ca]
    have hcenter (x y : Label n) :
        (∑ a : A, if a ca = y then
          (L a : ℂ) * (kappa l G (H.color e) (a ca).val x.val : ℂ) * centered x a else 0) = 0 := by
      by_cases hwel : WeldPair y x
      · calc
          _ = ∑ a : A, if a ca = y then (w x a : ℂ) *
              (f x a - conditionalMean (w x) (fun a => a ca) (f x) y) else 0 := by
            apply Finset.sum_congr rfl
            intro a _
            by_cases ha : a ca = y
            · simp only [ha, ite_true, centered, hwel, w, mean, Complex.ofReal_mul]
            · simp only [ha, ite_false]
          _ = 0 := conditional_centered (w x) (hw x) (fun a => a ca) (f x) y
      · apply Finset.sum_eq_zero
        intro a _
        by_cases ha : a ca = y
        · simp only [ha, ite_true, centered, hwel, ite_false, mul_zero]
        · simp only [ha, ite_false]
    let split : (Fin H.k → Label n) ≃ A × B :=
      Equiv.piEquivPiSubtypeProd P (fun _ => Label n)
    have hzero : (∑ φ : Fin H.k → Label n,
        (L (fun a => φ a) : ℂ) * (R (fun b => φ b) : ℂ) *
        (kappa l G (H.color e) (φ c).val (φ p).val : ℂ) *
        (centered (φ p) (fun a => φ a) * star (g (φ c) (fun b => φ b)))) = 0 := by
      apply weighted_bridge_fiber_centered_sum split (fun a => (L a : ℂ)) (fun b => (R b : ℂ))
        (fun a b => (kappa l G (H.color e) (a ca).val (b pb).val : ℂ))
        (fun a b => centered (b pb) a) (fun a => a ca) (fun y b => star (g y b))
      intro b y
      convert hcenter (b pb) y using 1
      apply Finset.sum_congr rfl
      intro a _
      split_ifs <;> rfl
    have hfactor (φ : Fin H.k → Label n) :
        maskedReference l G H allowed φ = referenceScale l G H *
          (L (fun a => φ a) * R (fun b => φ b) *
            kappa l G (H.color e) (φ c).val (φ p).val) := by
      rw [maskedReference_eq l G H hH allowed φ,
        forestWeight_bridge_branches H.E P (componentKernel l G H) support φ e he
          (fun q hq => hcut q (Finset.mem_erase.mp hq).2 (Finset.mem_erase.mp hq).1)]
      have hker : componentKernel l G H e (φ e.1) (φ e.2) =
          kappa l G (H.color e) (φ c).val (φ p).val := by
        rcases hends with rfl | rfl
        · rfl
        · exact KappaKernel.kappa_symm hG _ _ _
      rw [hker]
    rw [inner_lift _ (maskedReference_nonneg l G H hH allowed)]
    calc
      _ = (referenceScale l G H : ℂ) * (∑ φ : Fin H.k → Label n,
        (L (fun a => φ a) : ℂ) * (R (fun b => φ b) : ℂ) *
        (kappa l G (H.color e) (φ c).val (φ p).val : ℂ) *
        (centered (φ p) (fun a => φ a) * star (g (φ c) (fun b => φ b)))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro φ _
        rw [hr, hfactor]
        by_cases hwel : H.IsWeldUnder φ e
        · have hgeq : k φ = g (φ c) (fun b => φ b) := by
            simpa only [if_pos hwel] using hg φ
          rw [hrepr, hgeq]
          simp only [Complex.ofReal_mul]
          ring
        · have hreszero : residual φ = 0 := by simp [residual, hwel]
          rw [hreszero, ← hrepr, hreszero]
          simp
      _ = 0 := by rw [hzero, mul_zero]

/-- The local-space specialization, kept as the original public API. -/
theorem edge_split (l : ℕ) (G : WeldedInstance n) (hG : G.IsValid)
    (H : AbsForest n) (hH : H.IsValid) (allowed : Fin H.k → Label n → Prop)
    (e : Fin H.k × Fin H.k) (he : e ∈ H.E) (c p : Fin H.k)
    (hends : e = (c, p) ∨ e = (p, c)) (P : Fin H.k → Prop) [DecidablePred P]
    (hc : P c) (hp : ¬P p)
    (hcut : ∀ q ∈ H.E, q ≠ e → (P q.1 ↔ P q.2)) (h : Data H → ℂ) :
    ∃ r t : Data H → ℂ,
      (∀ φ : Fin H.k → Label n,
        h (H.Wfix φ c) = r (H.Wfix φ c) + t (H.Wfix φ p)) ∧
      (∀ φ : Fin H.k → Label n, ¬H.IsWeldUnder φ e → r (H.Wfix φ c) = 0) ∧
      (∀ v : Fin H.k, ¬P v → ∀ k : Data H → ℂ,
        inner ℂ
          (lift (maskedReference l G H allowed) (fun φ => k (H.Wfix φ v)))
          (lift (maskedReference l G H allowed) (fun φ => r (H.Wfix φ c))) = 0) := by
  obtain ⟨r, t, hsum, hsupp, horth⟩ :=
    edge_split_measurable l G hG H hH allowed e he c p hends P hc hp hcut h
  refine ⟨r, t, hsum, hsupp, ?_⟩
  intro v hv k
  apply horth (fun φ => k (H.Wfix φ v))
  obtain ⟨g, hg⟩ := weld_local_representation H hH e p c hends.symm (fun u => ¬P u)
    hp (fun q hq hqe => not_congr (hcut q hq hqe)) v hv k
  intro φ ψ hd
  dsimp only at hd ⊢
  rw [hg φ, hg ψ]
  exact congrArg (fun q => g q.1 q.2) hd

end WeldedPath.Supplement.EdgeCoefficientSplit

end

-- Solutions.WeldedPathFiberCollision
section

namespace WeldedPath.Supplement.FiberCollision

open Classical ConnectedConcentration FixedData EdgeCoefficientSplit
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}

noncomputable def avoidWeight (l : ℕ) (G : WeldedInstance n) (H : AbsForest n)
    (B : Finset ℕ) : (Fin H.k → Label n) → ℝ :=
  maskedReference l G H (fun _ x => x.val ∉ B)

theorem avoidWeight_nonneg (H : AbsForest n) (hH : H.IsValid) (B : Finset ℕ)
    (φ : Fin H.k → Label n) : 0 ≤ avoidWeight l G H B φ :=
  maskedReference_nonneg l G H hH _ φ

/-- On a nonempty fixed-data fiber in the all-avoid sector, the weight is
exactly the source's fixed-data/boundary-conditioned reference weight. -/
theorem fiber_weight_eq_source (H : AbsForest n) (hH : H.IsValid)
    (s : Fin H.k) (hs : ∀ u, H.graph.Reachable s u) (B : Finset ℕ)
    (φ₀ : Fin H.k → Label n) (havoid : ∀ u, (φ₀ u).val ∉ B)
    (φ : Fin H.k → Label n) :
    (if H.Wfix φ s = H.Wfix φ₀ s then avoidWeight l G H B φ else 0) =
      sourceWeight l G H φ₀ s B φ := by
  have hiff : (H.Wfix φ s = H.Wfix φ₀ s ∧ ∀ u, (φ u).val ∉ B) ↔
      (H.Wfix φ s = H.Wfix φ₀ s ∧
        ∀ u, H.graph.Reachable s u → u ∉ H.Ctree φ s → (φ u).val ∉ B) := by
    constructor
    · rintro ⟨hw, ha⟩
      exact ⟨hw, fun u _ _ => ha u⟩
    · rintro ⟨hw, ha⟩
      refine ⟨hw, ?_⟩
      intro u
      by_cases hu : u ∈ H.Ctree φ s
      · have hC : H.Ctree φ s = H.Ctree φ₀ s := congrArg Prod.fst hw
        have hu' : u ∈ H.Sfix φ₀ s := ctree_subset_sfix H φ₀ s (hC ▸ hu)
        have he := (wfix_eq_iff_agree_sfix H hH φ φ₀ s).mp hw u hu'
        simpa only [he] using havoid u
      · exact ha u (hs u) hu
  unfold avoidWeight maskedReference sourceWeight
  rw [← ite_and]
  by_cases h : H.Wfix φ s = H.Wfix φ₀ s ∧ ∀ u, (φ u).val ∉ B
  · simp only [if_pos h, if_pos (hiff.mp h)]
  · simp only [if_neg h, if_neg (mt hiff.mpr h)]

theorem same_data_sfix (H : AbsForest n) (hH : H.IsValid)
    (s : Fin H.k) (φ ψ : Fin H.k → Label n) (hw : H.Wfix φ s = H.Wfix ψ s) :
    H.Sfix φ s = H.Sfix ψ s :=
  sfix_eq_of_agree_sfix H hH φ ψ s ((wfix_eq_iff_agree_sfix H hH φ ψ s).mp hw)

/-- The actual free-collision estimate on every fixed-data fiber, in the
unnormalized form required to control arbitrary complex coefficients. -/
theorem free_collision_fiber_bound (H : AbsForest n) (hH : H.IsValid)
    (s : Fin H.k) (hs : ∀ u, H.graph.Reachable s u)
    (hG : G.IsValid) (hn : 16 ≤ n) (hl : 2 ≤ l) (hln : l ≤ n - 4)
    (B : Finset ℕ) (hB : Vbd n l ⊆ B) (hBw : Disjoint B (Vweld n))
    (hsmall : (H.k : ℝ) * (B.card : ℝ) * (4 / (2 : ℝ) ^ n) ≤ 1 / 2)
    (a b : Fin H.k) (d : FixedDataFunctions.Data H) :
    (∑ φ, if H.Wfix φ s = d ∧ FixedCollisions.FreeCollision H s a b φ then
      avoidWeight l G H B φ else 0) ≤
      (96 * ((n : ℝ) + 1) / (2 : ℝ) ^ n) *
        ∑ φ, if H.Wfix φ s = d then avoidWeight l G H B φ else 0 := by
  let μ := avoidWeight l G H B
  have hμ : ∀ φ, 0 ≤ μ φ := avoidWeight_nonneg H hH B
  have hden : 0 ≤ ∑ φ, if H.Wfix φ s = d then μ φ else 0 :=
    Finset.sum_nonneg fun φ _ => by split_ifs; exact hμ φ; rfl
  by_cases hab : a = b
  · simp only [hab, FixedCollisions.FreeCollision, FixedCollisions.Collision,
      ne_eq, not_true_eq_false, false_and, and_false, ite_false, Finset.sum_const_zero]
    exact mul_nonneg (by positivity) hden
  by_cases hwit : ∃ φ, H.Wfix φ s = d ∧ 0 < μ φ
  · obtain ⟨φ₀, hd₀, hpos⟩ := hwit
    have havoid : ∀ u, (φ₀ u).val ∉ B := by
      by_contra hh
      have hz : μ φ₀ = 0 := by simp only [μ, avoidWeight, maskedReference, if_neg hh]
      rw [hz] at hpos
      exact (lt_irrefl 0) hpos
    have href : H.muRef l G φ₀ ≠ 0 := by
      have hp : 0 < H.muRef l G φ₀ := by
        simpa only [μ, avoidWeight, maskedReference, if_pos havoid] using hpos
      exact ne_of_gt hp
    have heq (φ : Fin H.k → Label n) :
        (if H.Wfix φ s = d then μ φ else 0) = sourceWeight l G H φ₀ s B φ := by
      rw [← hd₀]
      exact fiber_weight_eq_source H hH s hs B φ₀ havoid φ
    by_cases hfixed : a ∈ H.Sfix φ₀ s ∧ b ∈ H.Sfix φ₀ s
    · have hzero : (∑ φ, if H.Wfix φ s = d ∧ FixedCollisions.FreeCollision H s a b φ
          then μ φ else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro φ _
        apply if_neg
        rintro ⟨hφ, hfree⟩
        have hS := same_data_sfix H hH s φ φ₀ (hφ.trans hd₀.symm)
        exact hfree.2 ⟨hS.symm ▸ hfixed.1, hS.symm ▸ hfixed.2⟩
      change (∑ φ, if H.Wfix φ s = d ∧ FixedCollisions.FreeCollision H s a b φ
        then μ φ else 0) ≤ _
      rw [hzero]
      exact mul_nonneg (by positivity) hden
    · have hfree : a ∉ H.Sfix φ₀ s ∨ b ∉ H.Sfix φ₀ s := not_and_or.mp hfixed
      have hbnd := ConditionalInjectivity.conditional_pair_collision_bound_of_free
        H hH φ₀ s hs hG hn hl hln href B hB hBw hsmall a b hab hfree
      have hsrc : ∀ φ, 0 ≤ sourceWeight l G H φ₀ s B φ := by
        intro φ
        rw [← heq φ]
        split_ifs
        · exact hμ φ
        · rfl
      have hD : 0 < ∑ φ, sourceWeight l G H φ₀ s B φ := by
        have hpos' : 0 < sourceWeight l G H φ₀ s B φ₀ := by
          rw [← heq φ₀, if_pos hd₀]
          exact hpos
        exact hpos'.trans_le (Finset.single_le_sum (fun φ _ => hsrc φ) (Finset.mem_univ φ₀))
      calc
        _ ≤ ∑ φ, if H.Wfix φ s = d ∧ φ a = φ b then μ φ else 0 := by
          apply Finset.sum_le_sum
          intro φ _
          by_cases hp : H.Wfix φ s = d ∧ FixedCollisions.FreeCollision H s a b φ
          · rw [if_pos hp, if_pos ⟨hp.1, hp.2.1.2⟩]
          · rw [if_neg hp]
            split_ifs
            · exact hμ φ
            · rfl
        _ = ∑ φ, if φ a = φ b then sourceWeight l G H φ₀ s B φ else 0 := by
          apply Finset.sum_congr rfl
          intro φ _
          rw [← heq φ]
          split_ifs <;> simp_all
        _ ≤ (96 * ((n : ℝ) + 1) / (2 : ℝ) ^ n) *
            ∑ φ, sourceWeight l G H φ₀ s B φ := (div_le_iff₀ hD).mp hbnd
        _ = _ := by simp_rw [← heq]; rfl
  · have hz : ∀ φ, H.Wfix φ s = d → μ φ = 0 := by
      intro φ hd
      exact le_antisymm (le_of_not_gt (fun hp => hwit ⟨φ, hd, hp⟩)) (hμ φ)
    have hnum : (∑ φ, if H.Wfix φ s = d ∧ FixedCollisions.FreeCollision H s a b φ
        then μ φ else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro φ _
      by_cases hd : H.Wfix φ s = d
      · simp only [hz φ hd, ite_self]
      · simp only [hd, false_and, ite_false]
    change (∑ φ, if H.Wfix φ s = d ∧ FixedCollisions.FreeCollision H s a b φ
      then μ φ else 0) ≤ _
    rw [hnum]
    exact mul_nonneg (by positivity) hden

end WeldedPath.Supplement.FiberCollision

end

-- Solutions.WeldedPathRootedCut
section

namespace WeldedPath.RootedCut

variable {V : Type*} (J : SimpleGraph V) (s : V)

theorem shortest_walk_avoids {u v : V} (p : J.Walk s u)
    (hp : p.length = J.dist s u) (hd : J.dist s u ≤ J.dist s v) (hne : v ≠ u) :
    v ∉ p.support := by
  classical
  intro hv
  have h₁ := J.dist_le (p.takeUntil v hv)
  have h₂ := p.length_takeUntil_lt_length hv hne
  omega

theorem reachable_delete_of_distance_le {u v : V} (w : V)
    (hu : J.Reachable s u) (hd : J.dist s u ≤ J.dist s v) (hne : v ≠ u) :
    (J.deleteEdges {s(v, w)}).Reachable s u := by
  classical
  obtain ⟨p, hp⟩ := hu.exists_walk_length_eq_dist
  have hv := shortest_walk_avoids J s p hp hd hne
  have he : s(v, w) ∉ p.edges := fun h => hv (p.fst_mem_support_of_mem_edges h)
  exact ⟨p.toDeleteEdge s(v, w) he⟩

/-- Every other vertex on the child side of a rooted tree edge has greater
root distance. This locates all earlier coefficient spaces outside that branch. -/
theorem distance_lt_on_child_side (hJ : J.IsAcyclic) {v p u : V}
    (hv : J.Reachable s v) (hvp : J.Adj v p)
    (hd : J.dist s p + 1 = J.dist s v)
    (hu : (J.deleteEdges {s(v, p)}).Reachable v u) (hne : u ≠ v) :
    J.dist s v < J.dist s u := by
  by_contra hh
  have hud : J.dist s u ≤ J.dist s v := le_of_not_gt hh
  have hur : J.Reachable s u := hv.trans (hu.mono (J.deleteEdges_le _))
  have hsu := reachable_delete_of_distance_le J s p hur hud hne.symm
  have hsp := reachable_delete_of_distance_le J s p (hv.trans hvp.reachable)
    (by omega) hvp.ne
  have hb := (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp hJ) hvp
  exact hb (hu.trans (hsu.symm.trans hsp))

end WeldedPath.RootedCut

end

-- Solutions.WeldedPathCoefficientOrder
section

namespace WeldedPath.Supplement.CoefficientOrder

open Classical FiniteWeightedForest ForestOrder

variable {n : ℕ} (H : AbsForest n) (hH : H.IsValid) (s : Fin H.k)

theorem exists_root_order (hconn : ∀ u, H.graph.Reachable s u) :
    ∃ order : Fin H.k ≃ Fin H.k,
      (∀ i j, H.graph.dist s (order i) < H.graph.dist s (order j) → i < j) ∧
      order ⟨0, by have := s.isLt; omega⟩ = s := by
  have hk : 0 < H.k := by have := s.isLt; omega
  obtain ⟨order, hord⟩ : ∃ order : Fin H.k ≃ Fin H.k,
      ∀ i j, H.graph.dist s (order i) < H.graph.dist s (order j) → i < j := by
    exact FiniteRankEnumeration.exists_rank_order_of_card_eq
      (fun v : Fin H.k => H.graph.dist s v) H.k (Fintype.card_fin H.k)
  refine ⟨order, hord, ?_⟩
  by_contra hn
  have hd : 0 < H.graph.dist s (order ⟨0, by omega⟩) := by
    apply Nat.pos_of_ne_zero
    intro hz
    exact hn ((hconn _).dist_eq_zero_iff.mp hz).symm
  have hi := hord (order.symm s) ⟨0, by omega⟩ (by simpa using hd)
  exact (Nat.not_lt_zero _ hi)

include hH in
/-- For every non-root vertex in distance order, its parent is earlier and
all earlier vertices lie outside its branch. This is the structural input
for peeling conditionally centered coefficient functions. -/
theorem earlier_parent_and_cut (hconn : ∀ u, H.graph.Reachable s u)
    (order : Fin H.k ≃ Fin H.k)
    (hord : ∀ i j, H.graph.dist s (order i) < H.graph.dist s (order j) → i < j)
    (i : Fin H.k) (hne : order i ≠ s) :
    ∃ j : Fin H.k, j < i ∧ ∃ e ∈ H.E,
      (e = (order i, order j) ∨ e = (order j, order i)) ∧
      ∃ P : Fin H.k → Prop, P (order i) ∧ ¬ P (order j) ∧
        (∀ p ∈ H.E, p ≠ e → (P p.1 ↔ P p.2)) ∧
        (∀ a : Fin H.k, a < i → ¬ P (order a)) := by
  let v := order i
  let p := rootParent H.graph s v
  let j := order.symm p
  have hj : order j = p := order.apply_symm_apply _
  have hp := rootParent_spec H.graph s (hconn v) hne
  have hpd : H.graph.dist s p + 1 = H.graph.dist s v := hp.2
  have hji : j < i := by
    apply hord
    rw [hj]
    change H.graph.dist s p < H.graph.dist s v
    omega
  obtain ⟨e, he, hor⟩ : ∃ e ∈ H.E, e = (v, p) ∨ e = (p, v) := by
    rcases hp.1 with ⟨_, he | he⟩
    · exact ⟨(v, p), he, Or.inl rfl⟩
    · exact ⟨(p, v), he, Or.inr rfl⟩
  have heq : s(e.1, e.2) = s(v, p) := by
    rcases hor with rfl | rfl
    · rfl
    · exact Sym2.eq_swap
  let J := H.graph.deleteEdges {s(v, p)}
  let P : Fin H.k → Prop := fun u => J.Reachable v u
  have hle : edgeGraph (H.E.erase e) ≤ J := by
    simpa only [heq, J, edgeGraph, AbsForest.graph] using
      edgeGraph_erase_le_delete H.E e hH.1 he
  have hnot : ¬ P p := (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp hH.2.1) hp.1
  refine ⟨j, hji, e, he, ?_, P, SimpleGraph.Reachable.refl _, ?_, ?_, ?_⟩
  · simpa only [hj] using hor
  · simpa only [hj] using hnot
  · intro e' he' hne'
    have ha : J.Adj e'.1 e'.2 := hle
      ⟨ne_of_lt (hH.1 e' he'), Or.inl (Finset.mem_erase.mpr ⟨hne', he'⟩)⟩
    exact ⟨fun h => h.trans ha.reachable, fun h => h.trans ha.reachable.symm⟩
  · intro a ha hPa
    have han : order a ≠ v := by
      intro he'
      have hai : a = i := order.injective he'
      subst a
      exact (lt_irrefl i) ha
    have hd := RootedCut.distance_lt_on_child_side H.graph s hH.2.1
      (hconn v) hp.1 hp.2 hPa han
    have hai := hord i a hd
    exact (lt_asymm ha hai)

end WeldedPath.Supplement.CoefficientOrder

end

-- Solutions.WeldedPathOrthogonalPeeling
section

namespace WeldedPath.CoefficientStability

open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

/-- Successively adjoining local coefficient spaces, ordered from root to leaves. -/
def initialSpace (A : ℕ → Submodule ℂ E) : ℕ → Submodule ℂ E
  | 0 => ⊥
  | k + 1 => initialSpace A k ⊔ A k

theorem le_prefix (A : ℕ → Submodule ℂ E) {i k : ℕ} (hi : i < k) :
    A i ≤ initialSpace A k := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases hik : i = k
    · subst i; exact le_sup_right
    · exact (ih (by omega)).trans le_sup_left

/-- Peeling off conditionally centered leaf functions gives an orthogonal-energy
decomposition. The three hypotheses express the local centering operation:
the residual remains local, its mean transfers towards the root, and the
residual is orthogonal to everything already closer to the root. -/
theorem orthogonal_peeling (A : ℕ → Submodule ℂ E) (center : ℕ → E → E)
    (hlocal : ∀ i x, x ∈ A i → center i x ∈ A i)
    (hmean : ∀ i x, x ∈ A i → x - center i x ∈ initialSpace A i)
    (horth : ∀ i x, x ∈ A i → center i x ∈ (initialSpace A i)ᗮ)
    (m : ℕ) (f : E) (hf : f ∈ initialSpace A m) :
    ∃ v : ℕ → E, (∀ i < m, v i ∈ A i) ∧
      (∑ i ∈ Finset.range m, v i) = f ∧
      (∑ i ∈ Finset.range m, ‖v i‖ ^ 2) = ‖f‖ ^ 2 := by
  induction m generalizing f with
  | zero =>
    have hf0 : f = 0 := hf
    subst f
    exact ⟨fun _ => 0, by simp, by simp, by simp⟩
  | succ m ih =>
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp hf
    let r := center m y
    let p := x + (y - r)
    have hp : p ∈ initialSpace A m := (initialSpace A m).add_mem hx (hmean m y hy)
    have hr : r ∈ (initialSpace A m)ᗮ := horth m y hy
    have hpr : p + r = f := by dsimp [p]; rw [← hxy]; abel
    obtain ⟨v, hv, hvs, hve⟩ := ih p hp
    let w : ℕ → E := fun i => if i = m then r else v i
    have hwi : ∀ i ∈ Finset.range m, w i = v i := by
      intro i hi
      have him : i ≠ m := Nat.ne_of_lt (Finset.mem_range.mp hi)
      simp only [w, if_neg him]
    have hws : (∑ i ∈ Finset.range m, w i) = p := by
      rw [Finset.sum_congr rfl hwi, hvs]
    have hwe : (∑ i ∈ Finset.range m, ‖w i‖ ^ 2) = ‖p‖ ^ 2 := by
      rw [← hve]
      exact Finset.sum_congr rfl
        (fun i hi => congrArg (fun z : E => ‖z‖ ^ 2) (hwi i hi))
    refine ⟨w, ?_, ?_, ?_⟩
    · intro i hi
      by_cases him : i = m
      · subst i
        simpa only [w, if_pos rfl] using hlocal m y hy
      · simpa only [w, if_neg him] using hv i (by omega)
    · rw [Finset.sum_range_succ, hws]
      simpa only [w, if_pos rfl] using hpr
    · rw [Finset.sum_range_succ, hwe]
      have hip : inner ℂ p r = 0 := ((initialSpace A m).mem_orthogonal r).mp hr p hp
      have he := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero p r hip
      rw [hpr] at he
      simpa only [w, if_pos rfl, pow_two] using he.symm

theorem mem_initialSpace_orthogonal (A : ℕ → Submodule ℂ E) (m : ℕ) (r : E)
    (h : ∀ i < m, ∀ x ∈ A i, inner ℂ x r = 0) :
    r ∈ (initialSpace A m)ᗮ := by
  induction m with
  | zero => simp [initialSpace]
  | succ m ih =>
    intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    have hr := ih (fun i hi => h i (by omega))
    rw [inner_add_left, ((initialSpace A m).mem_orthogonal r).mp hr y hy,
      h m (Nat.lt_succ_self _) z hz, add_zero]

/-- An existential centering construction is enough: no canonical choice
of coefficient representative is needed for the energy decomposition. -/
theorem orthogonal_peeling_of_splits (A : ℕ → Submodule ℂ E)
    (hsplit : ∀ i x, x ∈ A i → ∃ r, r ∈ A i ∧
      x - r ∈ initialSpace A i ∧ r ∈ (initialSpace A i)ᗮ)
    (m : ℕ) (f : E) (hf : f ∈ initialSpace A m) :
    ∃ v : ℕ → E, (∀ i < m, v i ∈ A i) ∧
      (∑ i ∈ Finset.range m, v i) = f ∧
      (∑ i ∈ Finset.range m, ‖v i‖ ^ 2) = ‖f‖ ^ 2 := by
  classical
  let center (i : ℕ) (x : E) :=
    if hx : x ∈ A i then Classical.choose (hsplit i x hx) else 0
  apply orthogonal_peeling A center _ _ _ m f hf
  · intro i x hx
    simpa only [center, dif_pos hx] using (Classical.choose_spec (hsplit i x hx)).1
  · intro i x hx
    simpa only [center, dif_pos hx] using (Classical.choose_spec (hsplit i x hx)).2.1
  · intro i x hx
    simpa only [center, dif_pos hx] using (Classical.choose_spec (hsplit i x hx)).2.2

end WeldedPath.CoefficientStability

end

-- Solutions.WeldedPathCoefficientDecomposition
section

namespace WeldedPath.Supplement.CoefficientDecomposition

open Classical CoefficientOrder EdgeCoefficientSplit FixedDataFunctions
open WeldedPath.WeightedCoefficients WeldedPath.CoefficientStability
open scoped BigOperators

variable {n : ℕ}

/-- Every sum of fixed-data coefficient spaces on a connected abstract tree
has a decomposition into local coefficients whose total energy is exactly
the energy of the sum. Arbitrary unary boundary restrictions are permitted. -/
theorem local_energy_decomposition (l : ℕ) (G : WeldedInstance n) (hG : G.IsValid)
    (H : AbsForest n) (hH : H.IsValid) (s : Fin H.k)
    (hconn : ∀ u, H.graph.Reachable s u) (allowed : Fin H.k → Label n → Prop)
    (f : Hil (Fin H.k → Label n))
    (hf : f ∈ ⨆ v, localCoefficientSpace H (maskedReference l G H allowed) v) :
    ∃ g : Fin H.k → Hil (Fin H.k → Label n),
      (∀ v, g v ∈ localCoefficientSpace H (maskedReference l G H allowed) v) ∧
      (∑ v, g v) = f ∧ (∑ v, ‖g v‖ ^ 2) = ‖f‖ ^ 2 := by
  let μ := maskedReference l G H allowed
  obtain ⟨order, hord, hroot⟩ := exists_root_order H s hconn
  let A : ℕ → Submodule ℂ (Hil (Fin H.k → Label n)) :=
    fun i => if hi : i < H.k then localCoefficientSpace H μ (order ⟨i, hi⟩) else ⊥
  have hA (i : Fin H.k) : A i.val = localCoefficientSpace H μ (order i) := by
    simp only [A, dif_pos i.isLt]
  have hsplit : ∀ i x, x ∈ A i → ∃ r, r ∈ A i ∧
      x - r ∈ initialSpace A i ∧ r ∈ (initialSpace A i)ᗮ := by
    intro i x hx
    by_cases hi : i < H.k
    · let ii : Fin H.k := ⟨i, hi⟩
      by_cases hr : order ii = s
      · have he : ii = ⟨0, by have := s.isLt; omega⟩ := order.injective (hr.trans hroot.symm)
        have hi0 : i = 0 := congrArg Fin.val he
        subst i
        exact ⟨x, hx, by simp, by simp [initialSpace]⟩
      · obtain ⟨j, hji, e, he, hends, P, hc, hp, hcut, hearlier⟩ :=
          earlier_parent_and_cut H hH s hconn order hord ii hr
        have hx' : x ∈ localCoefficientSpace H μ (order ii) := by rwa [hA ii] at hx
        obtain ⟨h, hh⟩ : ∃ h : Data H → ℂ,
            lift μ (fun φ => h (H.Wfix φ (order ii))) = x :=
          (mem_dataSpace μ (fun φ => H.Wfix φ (order ii)) x).mp hx'
        obtain ⟨r, t, hdec, _, horth⟩ :=
          edge_split l G hG H hH allowed e he (order ii) (order j) hends P hc hp hcut h
        let rv := lift μ (fun φ => r (H.Wfix φ (order ii)))
        let tv := lift μ (fun φ => t (H.Wfix φ (order j)))
        have heq : x = rv + tv := by
          rw [← hh]
          ext φ
          change (Real.sqrt (μ φ) : ℂ) * h (H.Wfix φ (order ii)) =
            (Real.sqrt (μ φ) : ℂ) * r (H.Wfix φ (order ii)) +
            (Real.sqrt (μ φ) : ℂ) * t (H.Wfix φ (order j))
          rw [hdec φ, mul_add]
        refine ⟨rv, ?_, ?_, ?_⟩
        · rw [hA ii]
          exact lift_mem_dataSpace μ (fun φ => H.Wfix φ (order ii)) r
        · have ht : tv ∈ A j.val := by
            rw [hA j]
            exact lift_mem_dataSpace μ (fun φ => H.Wfix φ (order j)) t
          have hs : x - rv = tv := by rw [heq]; abel
          rw [hs]
          exact (le_prefix A hji) ht
        · apply mem_initialSpace_orthogonal A i rv
          intro a hai y hy
          have ha : a < H.k := lt_trans hai hi
          let aa : Fin H.k := ⟨a, ha⟩
          have hy' : y ∈ localCoefficientSpace H μ (order aa) := by rwa [hA aa] at hy
          obtain ⟨k, hk⟩ := (mem_dataSpace μ (fun φ => H.Wfix φ (order aa)) y).mp hy'
          rw [← hk]
          exact horth (order aa) (hearlier aa hai) k
    · have hx0 : x = 0 := by simpa only [A, dif_neg hi, Submodule.mem_bot] using hx
      subst x
      exact ⟨0, by simp, by simp, by simp⟩
  have hsup : (⨆ v, localCoefficientSpace H μ v) ≤ initialSpace A H.k := by
    apply iSup_le
    intro v
    have h := le_prefix A (order.symm v).isLt
    rw [hA (order.symm v), Equiv.apply_symm_apply] at h
    exact h
  obtain ⟨v, hv, hvs, hve⟩ := orthogonal_peeling_of_splits A hsplit H.k f (hsup hf)
  let g : Fin H.k → Hil (Fin H.k → Label n) := fun u => v (order.symm u).val
  refine ⟨g, ?_, ?_, ?_⟩
  · intro u
    have h := hv (order.symm u).val (order.symm u).isLt
    rwa [hA (order.symm u), Equiv.apply_symm_apply] at h
  · change (∑ u, v (order.symm u).val) = f
    rw [Equiv.sum_comp order.symm (fun i : Fin H.k => v i.val), Fin.sum_univ_eq_sum_range]
    exact hvs
  · change (∑ u, ‖v (order.symm u).val‖ ^ 2) = ‖f‖ ^ 2
    rw [Equiv.sum_comp order.symm (fun i : Fin H.k => ‖v i.val‖ ^ 2),
      Fin.sum_univ_eq_sum_range (fun i : ℕ => ‖v i‖ ^ 2)]
    exact hve

end WeldedPath.Supplement.CoefficientDecomposition

end

-- Solutions.WeldedPathStableCoefficients
section

namespace WeldedPath.Supplement.StableCoefficients

open scoped BigOperators
open Classical FixedCollisions FiberCollision FixedDataFunctions
open WeldedPath.WeightedCoefficients WeldedPath.CollisionStability

variable {n l : ℕ} {G : WeldedInstance n}

/-- The actual stable coefficient representative for a connected abstract
forest in the all-avoid boundary sector. The only numerical assumptions are
the survival bound and the cubic collision budget. -/
theorem connected_stable_representative (H : AbsForest n) (hH : H.IsValid)
    (s : Fin H.k) (hs : ∀ u, H.graph.Reachable s u)
    (hG : G.IsValid) (hn : 16 ≤ n) (hl : 2 ≤ l) (hln : l ≤ n - 4)
    (B : Finset ℕ) (hB : Vbd n l ⊆ B) (hBw : Disjoint B (Vweld n))
    (hsurvive : (H.k : ℝ) * (B.card : ℝ) * (4 / (2 : ℝ) ^ n) ≤ 1 / 2)
    (hsmall : (H.k : ℝ) ^ 3 * (96 * ((n : ℝ) + 1) / (2 : ℝ) ^ n) ≤ 1 / 2)
    (f₀ : Hil (Fin H.k → Label n))
    (hf₀ : f₀ ∈ ⨆ v, localCoefficientSpace H (avoidWeight l G H B) v) :
    ∃! f : Hil (Fin H.k → Label n),
      f ∈ (⨆ v, localCoefficientSpace H (avoidWeight l G H B) v) ∧
      f ∈ ((⨆ v, localCoefficientSpace H (avoidWeight l G H B) v) ⊓
        (eventSpace Function.Injective)ᗮ)ᗮ ∧
      (eventSpace Function.Injective).starProjection f =
        (eventSpace Function.Injective).starProjection f₀ ∧
      ‖f‖ ^ 2 ≤ 2 * ‖(eventSpace Function.Injective).starProjection f₀‖ ^ 2 := by
  let μ := avoidWeight l G H B
  let data := fun v (φ : Fin H.k → Label n) => H.Wfix φ v
  let S := ⨆ v, localCoefficientSpace H μ v
  let pairEvent := fun ab : Fin H.k × Fin H.k => Collision H ab.1 ab.2
  let fixedEvent := fun (ab : Fin H.k × Fin H.k) v => FixedCollision H v ab.1 ab.2
  let ε : ℝ := 96 * ((n : ℝ) + 1) / (2 : ℝ) ^ n
  have hμ : ∀ φ, 0 ≤ μ φ := avoidWeight_nonneg H hH B
  have hε : 0 ≤ ε := by positivity
  have hfixed : ∀ (ab : Fin H.k × Fin H.k) v f,
      f ∈ dataSpace μ (data v) →
      (eventSpace (fixedEvent ab v)).starProjection f ∈ S ⊓ (eventSpace Function.Injective)ᗮ := by
    intro ab v f hf
    exact fixed_mask_mem_kernel H hH μ v ab.1 ab.2 f hf
  have hcap : ∀ (ab : Fin H.k × Fin H.k) v d,
      (∑ φ, if data v φ = d ∧ (pairEvent ab φ ∧ ¬fixedEvent ab v φ) then μ φ else 0) ≤
        ε * ∑ φ, if data v φ = d then μ φ else 0 := by
    intro ab v d
    have hv : ∀ u, H.graph.Reachable v u := fun u => (hs v).symm.trans (hs u)
    have hbnd := free_collision_fiber_bound H hH v hv hG hn hl hln B hB hBw hsurvive ab.1 ab.2 d
    calc
      _ = ∑ φ, if H.Wfix φ v = d ∧ FreeCollision H v ab.1 ab.2 φ then μ φ else 0 := by
        apply Finset.sum_congr rfl
        intro φ _
        dsimp only [data, pairEvent, fixedEvent]
        by_cases hd : H.Wfix φ v = d
        · by_cases hc : Collision H ab.1 ab.2 φ
          · by_cases hf : ab.1 ∈ H.Sfix φ v ∧ ab.2 ∈ H.Sfix φ v
            · simp [hd, hc, FixedCollision, FreeCollision, hf, hf.1, hf.2]
            · simp only [hd, hc, FixedCollision, FreeCollision, true_and, hf,
                not_false_eq_true, ite_true, ite_false]
          · simp [hd, hc, FixedCollision, FreeCollision]
        · simp [hd]
      _ ≤ _ := hbnd
  have hdecomp : ∀ f ∈ S, f ∈ (S ⊓ (eventSpace Function.Injective)ᗮ)ᗮ →
      ∃ v : Fin H.k → Hil (Fin H.k → Label n),
        (∀ i, v i ∈ dataSpace μ (data i)) ∧
        f = ∑ i, v i ∧ (∑ i, ‖v i‖ ^ 2) ≤ ‖f‖ ^ 2 := by
    intro f hf _
    obtain ⟨v, hv, hsum, henergy⟩ := CoefficientDecomposition.local_energy_decomposition
      l G hG H hH s hs (fun _ x => x.val ∉ B) f hf
    exact ⟨v, hv, hsum.symm, henergy.le⟩
  have hsmall' : (Fintype.card (Fin H.k × Fin H.k) : ℝ) *
      (Fintype.card (Fin H.k) : ℝ) * ε ≤ 1 / 2 := by
    calc
      _ = (H.k : ℝ) ^ 3 * ε := by
        simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
        ring
      _ ≤ _ := hsmall
  exact stable_representative_of_fiber_bounds μ hμ data S Function.Injective pairEvent fixedEvent
    (not_injective_iff_collision H) (fun _ _ _ h => h.1) hfixed ε hε hcap hdecomp hsmall' f₀ hf₀

end WeldedPath.Supplement.StableCoefficients

end

-- Solutions.WeldedPathSectorStability
section

namespace WeldedPath.SectorStability

open scoped BigOperators
open Classical WeightedCoefficients CoefficientStability HilbertSupport

variable {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype ι]

lemma partition_indicator_sum (P : ι → Ω → Prop) (hp : ∀ ω, ∃! i, P i ω)
    (ω : Ω) (r : ℝ) : (∑ i, if P i ω then r else 0) = r := by
  obtain ⟨i, hi, hu⟩ := hp ω
  rw [Finset.sum_eq_single i]
  · exact if_pos hi
  · intro j _ hji
    exact if_neg (fun hj => hji (hu j hj))
  · simp

lemma partition_energy (P : ι → Ω → Prop) (hp : ∀ ω, ∃! i, P i ω) (f : Hil Ω) :
    (∑ i, ‖(eventSpace (P i)).starProjection f‖ ^ 2) = ‖f‖ ^ 2 := by
  simp only [eventSpace_projection, EuclideanSpace.norm_sq_eq]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  calc
    _ = ∑ i, if P i ω then ‖f ω‖ ^ 2 else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : P i ω <;> simp [diagProj_apply, hi]
    _ = _ := partition_indicator_sum P hp ω _

lemma event_projections_commute (P Q : Ω → Prop) (f : Hil Ω) :
    (eventSpace P).starProjection ((eventSpace Q).starProjection f) =
      (eventSpace Q).starProjection ((eventSpace P).starProjection f) := by
  simp only [eventSpace_projection]
  ext ω
  simp only [diagProj_apply]
  split_ifs <;> rfl

lemma other_sector_projection_zero (P : ι → Ω → Prop) (hp : ∀ ω, ∃! i, P i ω)
    (i j : ι) (hji : j ≠ i) (f : Hil Ω) (hf : f ∈ eventSpace (P j)) :
    (eventSpace (P i)).starProjection f = 0 := by
  rw [eventSpace_projection]
  ext ω
  by_cases hi : P i ω
  · have hj : ¬P j ω := fun hj => hji ((hp ω).unique hj hi)
    simp only [diagProj_apply, if_pos hi, hf ω hj, PiLp.zero_apply]
  · simp [diagProj_apply, hi]

/-- Sector projection preserves the corresponding summand of a subspace
supported on a finite diagonal partition. -/
lemma sector_projection_mem (P : ι → Ω → Prop) (hp : ∀ ω, ∃! i, P i ω)
    (S : ι → Submodule ℂ (Hil Ω)) (hS : ∀ i, S i ≤ eventSpace (P i))
    (i : ι) (f : Hil Ω) (hf : f ∈ ⨆ j, S j) :
    (eventSpace (P i)).starProjection f ∈ S i := by
  have hm : (⨆ j, S j) ≤ (S i).comap (eventSpace (P i)).starProjection.toLinearMap := by
    apply iSup_le
    intro j v hv
    change (eventSpace (P i)).starProjection v ∈ S i
    by_cases hji : j = i
    · subst j
      rw [(eventSpace (P i)).starProjection_eq_self_iff.mpr (hS i hv)]
      exact hv
    · rw [other_sector_projection_zero P hp i j hji v (hS j hv)]
      exact (S i).zero_mem
  exact hm hf

/-- A minimal global representative restricts to a minimal representative
in every diagonal sector. -/
lemma sector_projection_minimal (P : ι → Ω → Prop) (hp : ∀ ω, ∃! i, P i ω)
    (S : ι → Submodule ℂ (Hil Ω)) (hS : ∀ i, S i ≤ eventSpace (P i))
    (Good : Ω → Prop) (i : ι) (f : Hil Ω)
    (hf : f ∈ ((⨆ j, S j) ⊓ (eventSpace Good)ᗮ)ᗮ) :
    (eventSpace (P i)).starProjection f ∈ (S i ⊓ (eventSpace Good)ᗮ)ᗮ := by
  intro z hz
  rw [← (eventSpace (P i)).inner_starProjection_left_eq_right,
    (eventSpace (P i)).starProjection_eq_self_iff.mpr (hS i hz.1)]
  exact (((⨆ j, S j) ⊓ (eventSpace Good)ᗮ).mem_orthogonal f).mp hf z
    ⟨(le_iSup S i) hz.1, hz.2⟩

/-- Stable minimal bounds on the individual sectors combine without a loss
depending on the number of sectors. -/
theorem stable_representative_of_sector_bounds
    (P : ι → Ω → Prop) (hp : ∀ ω, ∃! i, P i ω)
    (S : ι → Submodule ℂ (Hil Ω)) (hS : ∀ i, S i ≤ eventSpace (P i))
    (Good : Ω → Prop)
    (hlocal : ∀ i f, f ∈ S i → f ∈ (S i ⊓ (eventSpace Good)ᗮ)ᗮ →
      ‖f‖ ^ 2 ≤ 2 * ‖(eventSpace Good).starProjection f‖ ^ 2)
    (f₀ : Hil Ω) (hf₀ : f₀ ∈ ⨆ i, S i) :
    ∃! f : Hil Ω, f ∈ (⨆ i, S i) ∧
      f ∈ ((⨆ i, S i) ⊓ (eventSpace Good)ᗮ)ᗮ ∧
      (eventSpace Good).starProjection f = (eventSpace Good).starProjection f₀ ∧
      ‖f‖ ^ 2 ≤ 2 * ‖(eventSpace Good).starProjection f₀‖ ^ 2 := by
  apply stable_representative (⨆ i, S i) (eventSpace Good) ?_ f₀ hf₀
  intro f hfS hf
  have hbound : ‖f‖ ^ 2 ≤ 2 * ‖(eventSpace Good).starProjection f‖ ^ 2 := by
    calc
      _ = ∑ i, ‖(eventSpace (P i)).starProjection f‖ ^ 2 := (partition_energy P hp f).symm
      _ ≤ ∑ i, 2 * ‖(eventSpace Good).starProjection ((eventSpace (P i)).starProjection f)‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        exact hlocal i _ (sector_projection_mem P hp S hS i f hfS)
          (sector_projection_minimal P hp S hS Good i f hf)
      _ = 2 * ‖(eventSpace Good).starProjection f‖ ^ 2 := by
        simp_rw [event_projections_commute Good]
        rw [← Finset.mul_sum, partition_energy P hp]
  have hpy := (eventSpace Good).norm_sq_eq_add_norm_sq_starProjection f
  nlinarith

/-- Finite diagonal-partition glue for already-proved local stable
representatives. No invariance of a sector under the other sector masks is
assumed: it follows from the disjoint supports. -/
theorem stable_representative_of_sector_stability
    (P : ι → Ω → Prop) (hp : ∀ ω, ∃! i, P i ω)
    (S : ι → Submodule ℂ (Hil Ω)) (hS : ∀ i, S i ≤ eventSpace (P i))
    (Good : Ω → Prop)
    (hlocal : ∀ i f₀, f₀ ∈ S i → ∃ f : Hil Ω,
      f ∈ S i ∧ f ∈ (S i ⊓ (eventSpace Good)ᗮ)ᗮ ∧
      (eventSpace Good).starProjection f = (eventSpace Good).starProjection f₀ ∧
      ‖f‖ ^ 2 ≤ 2 * ‖(eventSpace Good).starProjection f₀‖ ^ 2)
    (f₀ : Hil Ω) (hf₀ : f₀ ∈ ⨆ i, S i) :
    ∃! f : Hil Ω, f ∈ (⨆ i, S i) ∧
      f ∈ ((⨆ i, S i) ⊓ (eventSpace Good)ᗮ)ᗮ ∧
      (eventSpace Good).starProjection f = (eventSpace Good).starProjection f₀ ∧
      ‖f‖ ^ 2 ≤ 2 * ‖(eventSpace Good).starProjection f₀‖ ^ 2 := by
  apply stable_representative_of_sector_bounds P hp S hS Good ?_ f₀ hf₀
  intro i f hfS hf
  obtain ⟨g, hgS, hg, hproj, hnorm⟩ := hlocal i f hfS
  have hgf : g = f := projection_injective_on_minimal (S i) (eventSpace Good)
    hgS hfS hg hf hproj
  simpa only [hgf] using hnorm

end WeldedPath.SectorStability

end

-- Solutions.WeldedPathAllBoundaryStability
section

namespace WeldedPath.Supplement.AllBoundaryStability

open Classical BoundarySector FixedCollisions
open WeldedPath.WeightedCoefficients WeldedPath.HilbertSupport
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}

theorem boundary_pattern_partition (H : AbsForest n) (B : Finset ℕ) :
    ∀ φ : Fin H.k → Label n, ∃! F : Finset (Fin H.k), boundaryPattern H B F φ := by
  intro φ
  refine ⟨Finset.univ.filter (fun u => (φ u).val ∈ B), ?_, ?_⟩
  · intro u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  · intro F hF
    ext u
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using (hF u).symm

theorem sectorSpace_le_event (H : AbsForest n) (B : Finset ℕ) (F : Finset (Fin H.k)) :
    sectorSpace l G H B F ≤ eventSpace (boundaryPattern H B F) := by
  apply iSup_le
  intro v f hf
  obtain ⟨h, rfl⟩ := hf
  intro φ hφ
  change ((eventSpace (fun φ => F ⊆ H.Ctree φ v)).starProjection
    (lift (sectorWeight l G H B F) (h ∘ (fun φ => H.Wfix φ v)))) φ = 0
  rw [eventSpace_projection]
  simp only [diagProj_apply]
  change (if F ⊆ H.Ctree φ v then
    (Real.sqrt (sectorWeight l G H B F φ) : ℂ) * h (H.Wfix φ v) else 0) = 0
  simp only [sectorWeight, if_neg hφ, Real.sqrt_zero, Complex.ofReal_zero, zero_mul, ite_self]

lemma sectorWeight_empty (H : AbsForest n) (B : Finset ℕ) :
    sectorWeight l G H B ∅ = FiberCollision.avoidWeight l G H B := by
  funext φ
  have hi : boundaryPattern H B ∅ φ ↔ ∀ u, (φ u).val ∉ B := by
    simp [boundaryPattern]
  unfold sectorWeight FiberCollision.avoidWeight EdgeCoefficientSplit.maskedReference
  by_cases h : boundaryPattern H B ∅ φ
  · exact (if_pos h).trans (if_pos (hi.mp h)).symm
  · exact (if_neg h).trans (if_neg (mt hi.mpr h)).symm

lemma sectorCoefficientMap_empty (H : AbsForest n) (B : Finset ℕ) (v : Fin H.k) :
    sectorCoefficientMap l G H B ∅ v =
      coefficientMap (FiberCollision.avoidWeight l G H B) (fun φ => H.Wfix φ v) := by
  apply LinearMap.ext
  intro h
  change (eventSpace (fun φ => (∅ : Finset (Fin H.k)) ⊆ H.Ctree φ v)).starProjection
    (lift (sectorWeight l G H B ∅) (h ∘ (fun φ => H.Wfix φ v))) =
      lift (FiberCollision.avoidWeight l G H B) (h ∘ (fun φ => H.Wfix φ v))
  rw [sectorWeight_empty H B]
  apply Submodule.starProjection_eq_self_iff.mpr
  intro φ hn
  exact (hn (Finset.empty_subset _)).elim

theorem sectorSpace_empty_eq (H : AbsForest n) (B : Finset ℕ) :
    sectorSpace l G H B ∅ =
      ⨆ v, localCoefficientSpace H (FiberCollision.avoidWeight l G H B) v := by
  apply iSup_congr
  intro v
  exact congrArg LinearMap.range (sectorCoefficientMap_empty H B v)

noncomputable def allSectorSpace (l : ℕ) (G : WeldedInstance n) (H : AbsForest n)
    (B : Finset ℕ) : Submodule ℂ (Hil (Fin H.k → Label n)) :=
  ⨆ F : Finset (Fin H.k), sectorSpace l G H B F

/-- The boundary patterns form orthogonal coordinate sectors. Combining the
empty-pattern and anchored-pattern results therefore costs no extra factor. -/
theorem connected_stable_representative (H : AbsForest n) (hH : H.IsValid)
    (s : Fin H.k) (hs : ∀ u, H.graph.Reachable s u)
    (hG : G.IsValid) (hn : 16 ≤ n) (hl : 2 ≤ l) (hln : l ≤ n - 4)
    (B : Finset ℕ) (hB : Vbd n l ⊆ B) (hBw : Disjoint B (Vweld n))
    (hsurvive : (H.k : ℝ) * (B.card : ℝ) * (4 / (2 : ℝ) ^ n) ≤ 1 / 2)
    (hsmall : (H.k : ℝ) ^ 3 * (96 * ((n : ℝ) + 1) / (2 : ℝ) ^ n) ≤ 1 / 2)
    (f₀ : Hil (Fin H.k → Label n)) (hf₀ : f₀ ∈ allSectorSpace l G H B) :
    ∃! f : Hil (Fin H.k → Label n),
      f ∈ allSectorSpace l G H B ∧
      f ∈ (allSectorSpace l G H B ⊓ (eventSpace Function.Injective)ᗮ)ᗮ ∧
      (eventSpace Function.Injective).starProjection f =
        (eventSpace Function.Injective).starProjection f₀ ∧
      ‖f‖ ^ 2 ≤ 2 * ‖(eventSpace Function.Injective).starProjection f₀‖ ^ 2 := by
  apply SectorStability.stable_representative_of_sector_stability
    (fun F : Finset (Fin H.k) => boundaryPattern H B F)
    (boundary_pattern_partition H B) (fun F => sectorSpace l G H B F)
    (sectorSpace_le_event H B) Function.Injective ?_ f₀ hf₀
  intro F f₀ hf₀
  by_cases hF : F = ∅
  · subst F
    have hf₀' : f₀ ∈ ⨆ v, localCoefficientSpace H (FiberCollision.avoidWeight l G H B) v := by
      simpa only [sectorSpace_empty_eq] using hf₀
    have hh := (StableCoefficients.connected_stable_representative H hH s hs hG hn hl hln
      B hB hBw hsurvive hsmall f₀ hf₀').exists
    simpa only [sectorSpace_empty_eq] using hh
  · obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hF
    have hsa : ∀ u, H.graph.Reachable a u := fun u => (hs a).symm.trans (hs u)
    have hk : (1 : ℝ) ≤ H.k := by
      have hkNat : 1 ≤ H.k := by have := a.isLt; omega
      exact_mod_cast hkNat
    have hkpow : (H.k : ℝ) ^ 2 ≤ (H.k : ℝ) ^ 3 := by
      calc
        _ = (H.k : ℝ) ^ 2 * 1 := (mul_one _).symm
        _ ≤ (H.k : ℝ) ^ 2 * H.k := mul_le_mul_of_nonneg_left hk (sq_nonneg _)
        _ = _ := by ring
    have hsmall' : (H.k : ℝ) ^ 2 * (96 * ((n : ℝ) + 1) / (2 : ℝ) ^ n) ≤ 1 / 2 :=
      (mul_le_mul_of_nonneg_right hkpow (by positivity)).trans hsmall
    exact (BoundarySector.sector_stable_representative H hH B F a ha hsa hG hn hl hln
      hB hBw hsurvive hsmall' f₀ hf₀).exists

end WeldedPath.Supplement.AllBoundaryStability

end

-- Solutions.WeldedPathConnectedDescriptionSpan
section

namespace WeldedPath.Supplement.DescriptionCoefficients

open Classical BoundarySector AllBoundaryStability ConnectedConcentration FixedData
open WeldedPath.WeightedCoefficients WeldedPath.HilbertSupport
open scoped BigOperators

variable {n : ℕ}

section Fibers

variable {Ω D : Type*} [Fintype Ω] [DecidableEq D]

noncomputable def fiberAmplitude (μ : Ω → ℝ) (data : Ω → D) (d : D) : Hil Ω :=
  lift μ (fun ω => if data ω = d then 1 else 0)

theorem lift_eq_sum_fibers (μ : Ω → ℝ) (data : Ω → D) (h : D → ℂ) :
    lift μ (h ∘ data) = ∑ d ∈ Finset.univ.image data, h d • fiberAmplitude μ data d := by
  ext ω
  simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul]
  change (Real.sqrt (μ ω) : ℂ) * h (data ω) =
    ∑ d ∈ Finset.univ.image data, h d * ((Real.sqrt (μ ω) : ℂ) * if data ω = d then 1 else 0)
  simp [mul_ite, Finset.mem_image_of_mem data (Finset.mem_univ ω), mul_comm]

theorem dataSpace_le_of_fibers (μ : Ω → ℝ) (data : Ω → D) (S : Submodule ℂ (Hil Ω))
    (hS : ∀ d, fiberAmplitude μ data d ∈ S) : dataSpace μ data ≤ S := by
  rintro f ⟨h, rfl⟩
  change lift μ (h ∘ data) ∈ S
  rw [lift_eq_sum_fibers]
  exact S.sum_mem (fun d _ => S.smul_mem _ (hS d))

end Fibers

noncomputable def treeBoundary (H : AbsForest n) (B : Finset ℕ)
    (φ₀ : Fin H.k → Label n) (v : Fin H.k) : Finset (Fin H.k) :=
  (H.Ctree φ₀ v).filter (fun u => (φ₀ u).val ∈ B)

noncomputable def sourceAmplitude (l : ℕ) (G : WeldedInstance n) (H : AbsForest n)
    (B : Finset ℕ) (v : Fin H.k) (φ₀ : Fin H.k → Label n) : Hil (Fin H.k → Label n) :=
  WithLp.toLp 2 (fun φ => (Real.sqrt (sourceWeight l G H φ₀ v B φ) : ℂ))

def connectedGenerators (l : ℕ) (G : WeldedInstance n) (H : AbsForest n) (B : Finset ℕ) :
    Set (Hil (Fin H.k → Label n)) :=
  {f | ∃ v φ₀, f = sourceAmplitude l G H B v φ₀}

theorem treeBoundary_pattern_iff (H : AbsForest n) (hH : H.IsValid)
    (B : Finset ℕ) (v : Fin H.k) (hs : ∀ u, H.graph.Reachable v u)
    (φ φ₀ : Fin H.k → Label n) (hw : H.Wfix φ v = H.Wfix φ₀ v) :
    boundaryPattern H B (treeBoundary H B φ₀ v) φ ↔
      ∀ u, H.graph.Reachable v u → u ∉ H.Ctree φ v → (φ u).val ∉ B := by
  have hC : H.Ctree φ v = H.Ctree φ₀ v := congrArg Prod.fst hw
  have hagree := (wfix_eq_iff_agree_sfix H hH φ φ₀ v).mp hw
  constructor
  · intro hp u _ hu hb
    have hm := Finset.mem_filter.mp ((hp u).mp hb)
    exact hu (hC.symm ▸ hm.1)
  · intro hav u
    by_cases hu : u ∈ H.Ctree φ₀ v
    · rw [hagree u (ctree_subset_sfix H φ₀ v hu)]
      simp only [treeBoundary, Finset.mem_filter, hu, true_and]
    · have hb := hav u (hs u) (fun h => hu (hC ▸ h))
      have hf : u ∉ treeBoundary H B φ₀ v := fun h => hu (Finset.mem_filter.mp h).1
      exact iff_of_false hb hf

theorem sourceWeight_eq_treeBoundary_fiber (l : ℕ) (G : WeldedInstance n)
    (H : AbsForest n) (hH : H.IsValid) (B : Finset ℕ) (v : Fin H.k)
    (hs : ∀ u, H.graph.Reachable v u) (φ₀ φ : Fin H.k → Label n) :
    sourceWeight l G H φ₀ v B φ = if H.Wfix φ v = H.Wfix φ₀ v then
      anchoredWeight l G H B (treeBoundary H B φ₀ v) v φ else 0 := by
  by_cases hw : H.Wfix φ v = H.Wfix φ₀ v
  · have hC : H.Ctree φ v = H.Ctree φ₀ v := congrArg Prod.fst hw
    have hsub : treeBoundary H B φ₀ v ⊆ H.Ctree φ v := by
      rw [hC]
      exact Finset.filter_subset _ _
    have hi := treeBoundary_pattern_iff H hH B v hs φ φ₀ hw
    unfold sourceWeight anchoredWeight sectorWeight
    rw [if_pos hw, if_pos hsub]
    by_cases hp : boundaryPattern H B (treeBoundary H B φ₀ v) φ
    · exact (if_pos ⟨hw, hi.mp hp⟩).trans (if_pos hp).symm
    · exact (if_neg (fun h => hp (hi.mpr h.2))).trans (if_neg hp).symm
  · simp only [sourceWeight, hw, false_and, if_false]

theorem sourceAmplitude_eq_fiber (l : ℕ) (G : WeldedInstance n)
    (H : AbsForest n) (hH : H.IsValid) (B : Finset ℕ) (v : Fin H.k)
    (hs : ∀ u, H.graph.Reachable v u) (φ₀ : Fin H.k → Label n) :
    sourceAmplitude l G H B v φ₀ =
      fiberAmplitude (anchoredWeight l G H B (treeBoundary H B φ₀ v) v)
        (fun φ => H.Wfix φ v) (H.Wfix φ₀ v) := by
  ext φ
  change (Real.sqrt (sourceWeight l G H φ₀ v B φ) : ℂ) =
    (Real.sqrt (anchoredWeight l G H B (treeBoundary H B φ₀ v) v φ) : ℂ) *
      if H.Wfix φ v = H.Wfix φ₀ v then 1 else 0
  rw [sourceWeight_eq_treeBoundary_fiber l G H hH B v hs φ₀ φ]
  by_cases hw : H.Wfix φ v = H.Wfix φ₀ v <;>
    simp only [hw, if_true, if_false, mul_one, mul_zero, Real.sqrt_zero, Complex.ofReal_zero]

theorem sourceAmplitude_mem_allSector (l : ℕ) (G : WeldedInstance n)
    (H : AbsForest n) (hH : H.IsValid) (B : Finset ℕ) (v : Fin H.k)
    (hs : ∀ u, H.graph.Reachable v u) (φ₀ : Fin H.k → Label n) :
    sourceAmplitude l G H B v φ₀ ∈ allSectorSpace l G H B := by
  apply (le_iSup (fun F => sectorSpace l G H B F) (treeBoundary H B φ₀ v))
  apply (le_iSup (fun u => LinearMap.range
    (sectorCoefficientMap l G H B (treeBoundary H B φ₀ v) u)) v)
  refine ⟨fun d => if d = H.Wfix φ₀ v then 1 else 0, ?_⟩
  rw [anchor_generator_eq, sourceAmplitude_eq_fiber l G H hH B v hs φ₀]
  rfl

lemma treeBoundary_eq_of_pattern (H : AbsForest n) (B : Finset ℕ)
    (F : Finset (Fin H.k)) (φ₀ : Fin H.k → Label n) (v : Fin H.k)
    (hp : boundaryPattern H B F φ₀) (hF : F ⊆ H.Ctree φ₀ v) :
    treeBoundary H B φ₀ v = F := by
  ext u
  simp only [treeBoundary, Finset.mem_filter]
  exact ⟨fun h => (hp u).mp h.2, fun h => ⟨hF h, (hp u).mpr h⟩⟩

/-- The connected all-sector coefficient space is exactly the span of
the unprojected fixed-data/boundary description amplitudes. -/
theorem allSectorSpace_eq_connectedSpan (l : ℕ) (G : WeldedInstance n)
    (H : AbsForest n) (hH : H.IsValid) (B : Finset ℕ)
    (hconn : ∀ v u, H.graph.Reachable v u) :
    allSectorSpace l G H B = Submodule.span ℂ (connectedGenerators l G H B) := by
  apply le_antisymm
  · apply iSup_le
    intro F
    apply iSup_le
    intro v f hf
    obtain ⟨h, rfl⟩ := hf
    rw [anchor_generator_eq]
    apply dataSpace_le_of_fibers (anchoredWeight l G H B F v) (fun φ => H.Wfix φ v)
      (Submodule.span ℂ (connectedGenerators l G H B)) ?_ (lift_mem_dataSpace _ _ h)
    intro d
    by_cases hx : ∃ φ₀, H.Wfix φ₀ v = d ∧ anchoredWeight l G H B F v φ₀ ≠ 0
    · obtain ⟨φ₀, hd, hne⟩ := hx
      have hF : F ⊆ H.Ctree φ₀ v := by
        by_contra hn
        exact hne (by simp only [anchoredWeight, if_neg hn])
      have hp : boundaryPattern H B F φ₀ := by
        by_contra hn
        exact hne (by simp only [anchoredWeight, if_pos hF, sectorWeight, if_neg hn])
      have he := sourceAmplitude_eq_fiber l G H hH B v (hconn v) φ₀
      rw [treeBoundary_eq_of_pattern H B F φ₀ v hp hF, hd] at he
      rw [← he]
      exact Submodule.subset_span ⟨v, φ₀, rfl⟩
    · have hz : fiberAmplitude (anchoredWeight l G H B F v) (fun φ => H.Wfix φ v) d = 0 := by
        ext φ
        change (Real.sqrt (anchoredWeight l G H B F v φ) : ℂ) *
          (if H.Wfix φ v = d then 1 else 0) = 0
        by_cases hd : H.Wfix φ v = d
        · have hzero : anchoredWeight l G H B F v φ = 0 :=
            Classical.byContradiction (fun hn => hx ⟨φ, hd, hn⟩)
          simp only [hzero, Real.sqrt_zero, Complex.ofReal_zero, zero_mul]
        · simp only [if_neg hd, mul_zero]
      rw [hz]
      exact Submodule.zero_mem _
  · apply Submodule.span_le.mpr
    rintro f ⟨v, φ₀, rfl⟩
    exact sourceAmplitude_mem_allSector l G H hH B v (hconn v) φ₀

end WeldedPath.Supplement.DescriptionCoefficients

end

-- Solutions.WeldedPathDescriptionCoordinates
section

namespace WeldedPath.Supplement.DescriptionCoefficients

open Classical ComponentForest ComponentRestriction ForestFactorization ConnectedConcentration
open scoped BigOperators

variable {n : ℕ}

noncomputable def selection (H : AbsForest n)
    (sel : (s : Roots H) → Fin (H.comp s.val).card) : Finset (Fin H.k) :=
  Finset.univ.image (fun s => vertexMap H s.val (sel s))

noncomputable def rootDescription (H : AbsForest n)
    (sel : (s : Roots H) → Fin (H.comp s.val).card)
    (ref : (s : Roots H) → LocalAssignment H s) : Description n :=
  ⟨H, selection H sel, (assignmentEquiv H).symm ref⟩

lemma reachable_vertexMap_iff (H : AbsForest n) (s : Fin H.k)
    (i : Fin (H.comp s).card) (u : Fin H.k) :
    H.graph.Reachable (vertexMap H s i) u ↔ u ∈ H.comp s := by
  have hi := (Finset.mem_filter.mp (vertexMap_mem H s i)).2
  exact ⟨fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi.trans h⟩,
    fun h => hi.symm.trans (Finset.mem_filter.mp h).2⟩

theorem rootDescription_valid (H : AbsForest n) (hH : H.IsValid)
    (sel : (s : Roots H) → Fin (H.comp s.val).card)
    (ref : (s : Roots H) → LocalAssignment H s) : (rootDescription H sel ref).IsValid := by
  refine ⟨hH, ?_⟩
  intro u
  let a : Roots H := ⟨compRoot H u, compRoot_isRoot H u⟩
  have hau : H.graph.Reachable a.val u := compRoot_reachable H u
  have hsel (s : Roots H) : H.graph.Reachable s.val (vertexMap H s.val (sel s)) :=
    (Finset.mem_filter.mp (vertexMap_mem H s.val (sel s))).2
  refine ⟨vertexMap H a.val (sel a), ⟨Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩,
    hau.symm.trans (hsel a)⟩, ?_⟩
  rintro v ⟨hv, huv⟩
  obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hv
  have habr := hau.trans (huv.trans (hsel b).symm)
  have hab : a = b := Subtype.ext (le_antisymm (a.property _ habr) (b.property _ habr.symm))
  cases hab
  rfl

noncomputable def chosenVertex (H : AbsForest n) (sel : Finset (Fin H.k))
    (φ₀ : Fin H.k → Label n) (hD : (Description.mk H sel φ₀).IsValid) (r : Roots H) :
    Fin H.k := Classical.choose (hD.2 r.val)

lemma chosenVertex_spec (H : AbsForest n) (sel : Finset (Fin H.k))
    (φ₀ : Fin H.k → Label n) (hD : (Description.mk H sel φ₀).IsValid) (r : Roots H) :
    chosenVertex H sel φ₀ hD r ∈ sel ∧ H.graph.Reachable r.val (chosenVertex H sel φ₀ hD r) :=
  (Classical.choose_spec (hD.2 r.val)).1

noncomputable def chosenIndex (H : AbsForest n) (sel : Finset (Fin H.k))
    (φ₀ : Fin H.k → Label n) (hD : (Description.mk H sel φ₀).IsValid) (r : Roots H) :
    Fin (H.comp r.val).card :=
  (vertexEquiv H r.val).symm ⟨chosenVertex H sel φ₀ hD r,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, (chosenVertex_spec H sel φ₀ hD r).2⟩⟩

@[simp] theorem vertexMap_chosenIndex (H : AbsForest n) (sel : Finset (Fin H.k))
    (φ₀ : Fin H.k → Label n) (hD : (Description.mk H sel φ₀).IsValid) (r : Roots H) :
    vertexMap H r.val (chosenIndex H sel φ₀ hD r) = chosenVertex H sel φ₀ hD r := by
  simp only [vertexMap, chosenIndex, OrderIso.apply_symm_apply]

theorem selection_chosenIndex (H : AbsForest n) (sel : Finset (Fin H.k))
    (φ₀ : Fin H.k → Label n) (hD : (Description.mk H sel φ₀).IsValid) :
    selection H (chosenIndex H sel φ₀ hD) = sel := by
  ext u
  constructor
  · intro hu
    obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hu
    rw [vertexMap_chosenIndex]
    exact (chosenVertex_spec H sel φ₀ hD r).1
  · intro hu
    let r : Roots H := ⟨compRoot H u, compRoot_isRoot H u⟩
    have he : u = chosenVertex H sel φ₀ hD r :=
      (Classical.choose_spec (hD.2 r.val)).2 u ⟨hu, compRoot_reachable H u⟩
    exact Finset.mem_image.mpr ⟨r, Finset.mem_univ _, (vertexMap_chosenIndex H sel φ₀ hD r).trans he.symm⟩

theorem rootDescription_chosen (H : AbsForest n) (sel : Finset (Fin H.k))
    (φ₀ : Fin H.k → Label n) (hD : (Description.mk H sel φ₀).IsValid) :
    rootDescription H (chosenIndex H sel φ₀ hD) (assignmentEquiv H φ₀) =
      Description.mk H sel φ₀ := by
  simp only [rootDescription, selection_chosenIndex, Equiv.symm_apply_apply]

theorem component_condition_iff (H : AbsForest n) (hH : H.IsValid) (B : Finset ℕ)
    (r : Roots H) (v : Fin (H.comp r.val).card)
    (φ φ₀ : Fin H.k → Label n) :
    ((componentForest H r.val).Wfix (restrict H r.val φ) v =
        (componentForest H r.val).Wfix (restrict H r.val φ₀) v ∧
      ∀ u, (componentForest H r.val).graph.Reachable v u →
        u ∉ (componentForest H r.val).Ctree (restrict H r.val φ) v →
          (restrict H r.val φ u).val ∉ B) ↔
    (H.Wfix φ (vertexMap H r.val v) = H.Wfix φ₀ (vertexMap H r.val v) ∧
      ∀ u, H.graph.Reachable (vertexMap H r.val v) u →
        u ∉ H.Ctree φ (vertexMap H r.val v) → (φ u).val ∉ B) := by
  rw [wfix_fiber_iff H hH r.val]
  apply and_congr_right
  intro _
  have hlocal :
      (∀ u, (componentForest H r.val).graph.Reachable v u →
        u ∉ (componentForest H r.val).Ctree (restrict H r.val φ) v →
          (restrict H r.val φ u).val ∉ B) ↔
      (∀ u, u ∉ (componentForest H r.val).Ctree (restrict H r.val φ) v →
          (restrict H r.val φ u).val ∉ B) :=
    ⟨fun h u => h u (component_connected H r.val v u), fun h u _ => h u⟩
  rw [hlocal, avoid_ctree_restrict_iff]
  constructor
  · intro h u hu
    exact h u ((reachable_vertexMap_iff H r.val v u).mp hu)
  · intro h u hu
    exact h u ((reachable_vertexMap_iff H r.val v u).mpr hu)

theorem description_condition_iff (H : AbsForest n) (hH : H.IsValid) (B : Finset ℕ)
    (sel : (r : Roots H) → Fin (H.comp r.val).card)
    (ref : (r : Roots H) → LocalAssignment H r) (φ : Fin H.k → Label n) :
    ((∀ s ∈ selection H sel, H.Wfix φ s = H.Wfix ((assignmentEquiv H).symm ref) s) ∧
      (∀ s ∈ selection H sel, ∀ u, H.graph.Reachable s u →
        u ∉ H.Ctree φ s → (φ u).val ∉ B)) ↔
    ∀ r : Roots H,
      (componentForest H r.val).Wfix (restrict H r.val φ) (sel r) =
          (componentForest H r.val).Wfix (ref r) (sel r) ∧
        ∀ u, (componentForest H r.val).graph.Reachable (sel r) u →
          u ∉ (componentForest H r.val).Ctree (restrict H r.val φ) (sel r) →
            (restrict H r.val φ u).val ∉ B := by
  have he (r : Roots H) := component_condition_iff H hH B r (sel r) φ
    ((assignmentEquiv H).symm ref)
  simp only [restrict_assignmentEquiv_symm] at he
  constructor
  · rintro ⟨hw, hb⟩ r
    have hr : vertexMap H r.val (sel r) ∈ selection H sel :=
      Finset.mem_image.mpr ⟨r, Finset.mem_univ _, rfl⟩
    exact (he r).mpr ⟨hw _ hr, hb _ hr⟩
  · intro h
    constructor
    · intro s hs
      obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hs
      exact ((he r).mp (h r)).1
    · intro s hs
      obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hs
      exact ((he r).mp (h r)).2

theorem descriptionWeight_eq_component_sources (l : ℕ) (G : WeldedInstance n)
    (H : AbsForest n) (hH : H.IsValid) (B : Finset ℕ)
    (sel : (r : Roots H) → Fin (H.comp r.val).card)
    (ref : (r : Roots H) → LocalAssignment H r) (φ : Fin H.k → Label n) :
    descriptionWeight l G B (rootDescription H sel ref) φ =
      ∏ r : Roots H, sourceWeight l G (componentForest H r.val) (ref r) (sel r) B
        (restrict H r.val φ) := by
  let Q (r : Roots H) : Prop :=
    (componentForest H r.val).Wfix (restrict H r.val φ) (sel r) =
        (componentForest H r.val).Wfix (ref r) (sel r) ∧
      ∀ u, (componentForest H r.val).graph.Reachable (sel r) u →
        u ∉ (componentForest H r.val).Ctree (restrict H r.val φ) (sel r) →
          (restrict H r.val φ u).val ∉ B
  have hcond := description_condition_iff H hH B sel ref φ
  change _ ↔ ∀ r, Q r at hcond
  change (if (∀ s ∈ selection H sel, H.Wfix φ s = H.Wfix ((assignmentEquiv H).symm ref) s) ∧
      (∀ s ∈ selection H sel, ∀ u, H.graph.Reachable s u →
        u ∉ H.Ctree φ s → (φ u).val ∉ B) then H.muRef l G φ else 0) =
    ∏ r : Roots H, if Q r then (componentForest H r.val).muRef l G (restrict H r.val φ) else 0
  rw [Finset.prod_ite_zero]
  simp only [Finset.mem_univ, forall_const]
  by_cases hq : ∀ r, Q r
  · rw [if_pos hq, if_pos (hcond.mpr hq)]
    simpa only [assignmentEquiv_restrict] using muRef_eq_product_coordinates l G H hH φ
  · rw [if_neg hq, if_neg (fun h => hq (hcond.mp h))]

theorem product_sourceAmplitudes (l : ℕ) (G : WeldedInstance n)
    (H : AbsForest n) (hH : H.IsValid) (B : Finset ℕ)
    (sel : (r : Roots H) → Fin (H.comp r.val).card)
    (ref : (r : Roots H) → LocalAssignment H r) :
    productAmplitude H (fun r => sourceAmplitude l G (componentForest H r.val) B (sel r) (ref r)) =
      amplitude l G H B (selection H sel) ((assignmentEquiv H).symm ref) := by
  ext φ
  change (∏ r : Roots H,
    (Real.sqrt (sourceWeight l G (componentForest H r.val) (ref r) (sel r) B
      (restrict H r.val φ)) : ℂ)) =
    (Real.sqrt (descriptionWeight l G B (rootDescription H sel ref) φ) : ℂ)
  rw [descriptionWeight_eq_component_sources l G H hH B sel ref φ]
  have hn (r : Roots H) : 0 ≤ sourceWeight l G (componentForest H r.val)
      (ref r) (sel r) B (restrict H r.val φ) := by
    unfold sourceWeight
    split_ifs
    · exact muRef_nonneg l G _ (component_valid H hH r.val) _
    · exact le_rfl
  rw [Real.sqrt_prod Finset.univ (fun r _ => hn r), Complex.ofReal_prod]

theorem product_sourceAmplitudes_chosen (l : ℕ) (G : WeldedInstance n)
    (H : AbsForest n) (B : Finset ℕ) (sel : Finset (Fin H.k)) (φ₀ : Fin H.k → Label n)
    (hD : (Description.mk H sel φ₀).IsValid) :
    productAmplitude H (fun r => sourceAmplitude l G (componentForest H r.val) B
      (chosenIndex H sel φ₀ hD r) (assignmentEquiv H φ₀ r)) =
      amplitude l G H B sel φ₀ := by
  have h := product_sourceAmplitudes l G H hD.1 B (chosenIndex H sel φ₀ hD) (assignmentEquiv H φ₀)
  simpa only [selection_chosenIndex, Equiv.symm_apply_apply] using h

end WeldedPath.Supplement.DescriptionCoefficients

end

-- Solutions.ComponentProductSpan
section

namespace WeldedPath.Supplement.ComponentForest

open Classical
open scoped BigOperators

variable {I : Type*} [Fintype I] {X : I → Type*} [∀ i, Fintype (X i)]

noncomputable def piAtMap (f : (i : I) → Hil (X i)) (i : I) :
    Hil (X i) →ₗ[ℂ] Hil ((j : I) → X j) where
  toFun v := WithLp.toLp 2 (fun z => v (z i) * ∏ j ∈ Finset.univ.erase i, f j (z j))
  map_add' v w := by
    ext z
    change (v (z i) + w (z i)) * _ = v (z i) * _ + w (z i) * _
    ring
  map_smul' c v := by
    ext z
    change (c * v (z i)) * _ = c * (v (z i) * _)
    ring

lemma piAmplitude_update (f : (i : I) → Hil (X i)) (i : I) (v : Hil (X i)) :
    piAmplitude (Function.update f i v) = piAtMap f i v := by
  ext z
  change (∏ j, (Function.update f i v) j (z j)) =
    v (z i) * ∏ j ∈ Finset.univ.erase i, f j (z j)
  rw [← Finset.mul_prod_erase Finset.univ (fun j => (Function.update f i v) j (z j))
    (Finset.mem_univ i), Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]

theorem piSpace_spans (A : (i : I) → Set (Hil (X i))) :
    piSpace (fun i => Submodule.span ℂ (A i)) =
      Submodule.span ℂ {v | ∃ f : (i : I) → Hil (X i),
        (∀ i, f i ∈ A i) ∧ v = piAmplitude f} := by
  let U := Submodule.span ℂ {v | ∃ f : (i : I) → Hil (X i),
    (∀ i, f i ∈ A i) ∧ v = piAmplitude f}
  have hrec (s : Finset I) : ∀ f : (i : I) → Hil (X i),
      (∀ i ∈ s, f i ∈ Submodule.span ℂ (A i)) →
      (∀ i, i ∉ s → f i ∈ A i) → piAmplitude f ∈ U := by
    induction s using Finset.induction_on with
    | empty =>
      intro f hs hn
      exact Submodule.subset_span ⟨f, fun i => hn i (Finset.notMem_empty i), rfl⟩
    | @insert i s hi ih =>
      intro f hs hn
      have hlin : Submodule.span ℂ (A i) ≤ U.comap (piAtMap f i) := by
        apply Submodule.span_le.mpr
        intro v hv
        change piAtMap f i v ∈ U
        rw [← piAmplitude_update]
        apply ih
        · intro j hj
          have hji : j ≠ i := fun h => hi (h ▸ hj)
          simpa only [Function.update_of_ne hji] using hs j (Finset.mem_insert_of_mem hj)
        · intro j hj
          by_cases hji : j = i
          · subst j
            simpa only [Function.update_self] using hv
          · simpa only [Function.update_of_ne hji] using hn j (by simp only
              [Finset.mem_insert, not_or, hji, hj, not_false_eq_true, and_self])
      have hm := hlin (hs i (Finset.mem_insert_self i s))
      change piAtMap f i (f i) ∈ U at hm
      simpa only [← piAmplitude_update, Function.update_eq_self] using hm
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro v ⟨f, hf, rfl⟩
    exact hrec Finset.univ f (fun i _ => hf i) (fun i hi => (hi (Finset.mem_univ i)).elim)
  · apply Submodule.span_le.mpr
    rintro v ⟨f, hf, rfl⟩
    exact Submodule.subset_span ⟨f, fun i => Submodule.subset_span (hf i), rfl⟩

theorem productSpace_spans {n : ℕ} (H : AbsForest n)
    (A : (r : Roots H) → Set (Hil (LocalAssignment H r))) :
    productSpace H (fun r => Submodule.span ℂ (A r)) =
      Submodule.span ℂ {v | ∃ f : (r : Roots H) → Hil (LocalAssignment H r),
        (∀ r, f r ∈ A r) ∧ v = productAmplitude H f} := by
  let L : Hil ((r : Roots H) → LocalAssignment H r) →ₗ[ℂ] Hil (Fin H.k → Label n) :=
    (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (assignmentEquiv H).symm).toLinearMap
  have hL (f : (r : Roots H) → Hil (LocalAssignment H r)) :
      L (piAmplitude f) = productAmplitude H f := rfl
  have hm (S : (r : Roots H) → Submodule ℂ (Hil (LocalAssignment H r))) :
      (piSpace S).map L = productSpace H S := by
    rw [piSpace, productSpace, Submodule.map_span]
    apply congrArg (Submodule.span ℂ)
    ext v
    constructor
    · rintro ⟨w, ⟨f, hf, rfl⟩, rfl⟩
      exact ⟨f, hf, hL f⟩
    · rintro ⟨f, hf, rfl⟩
      exact ⟨piAmplitude f, ⟨f, hf, rfl⟩, hL f⟩
  rw [← hm, piSpace_spans, Submodule.map_span]
  apply congrArg (Submodule.span ℂ)
  ext v
  constructor
  · rintro ⟨w, ⟨f, hf, rfl⟩, rfl⟩
    exact ⟨f, hf, hL f⟩
  · rintro ⟨f, hf, rfl⟩
    exact ⟨piAmplitude f, ⟨f, hf, rfl⟩, hL f⟩

end WeldedPath.Supplement.ComponentForest

end

-- Solutions.WeldedPathDescriptionSpan
section

namespace WeldedPath.Supplement.DescriptionCoefficients

open Classical ComponentForest AllBoundaryStability

variable {n : ℕ}

/-- The full source coefficient space, with arbitrary connected
components and boundary sectors, is exactly the span of the canonical
fixed-forest description amplitudes before imposing injectivity. -/
theorem coefficientSpace_eq_descriptionSpan (l : ℕ) (G : WeldedInstance n)
    (H : AbsForest n) (hH : H.IsValid) (B : Finset ℕ) :
    productSpace H (fun r : Roots H => allSectorSpace l G (componentForest H r.val) B) =
      descriptionSpan l G H B := by
  have hspaces :
      (fun r : Roots H => allSectorSpace l G (componentForest H r.val) B) =
      (fun r : Roots H => Submodule.span ℂ
        (connectedGenerators l G (componentForest H r.val) B)) := by
    funext r
    exact allSectorSpace_eq_connectedSpan l G _ (component_valid H hH r.val) B
      (component_connected H r.val)
  rw [hspaces, productSpace_spans, descriptionSpan]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro v ⟨f, hf, rfl⟩
    simp only [connectedGenerators, Set.mem_setOf_eq] at hf
    choose sel ref he using hf
    have heq : f = fun r => sourceAmplitude l G (componentForest H r.val) B (sel r) (ref r) :=
      funext he
    rw [heq, product_sourceAmplitudes l G H hH B sel ref]
    exact Submodule.subset_span ⟨selection H sel, (assignmentEquiv H).symm ref,
      rootDescription_valid H hH sel ref, rfl⟩
  · apply Submodule.span_le.mpr
    rintro v ⟨sel, φ₀, hD, rfl⟩
    rw [← product_sourceAmplitudes_chosen l G H B sel φ₀ hD]
    exact Submodule.subset_span ⟨fun r => sourceAmplitude l G (componentForest H r.val) B
      (chosenIndex H sel φ₀ hD r) (assignmentEquiv H φ₀ r),
      fun r => ⟨chosenIndex H sel φ₀ hD r, assignmentEquiv H φ₀ r, rfl⟩, rfl⟩

theorem amplitude_mem_coefficientSpace (l : ℕ) (G : WeldedInstance n)
    (H : AbsForest n) (B : Finset ℕ) (sel : Finset (Fin H.k)) (φ₀ : Fin H.k → Label n)
    (hD : (Description.mk H sel φ₀).IsValid) :
    amplitude l G H B sel φ₀ ∈
      productSpace H (fun r : Roots H => allSectorSpace l G (componentForest H r.val) B) := by
  rw [coefficientSpace_eq_descriptionSpan l G H hD.1 B]
  exact Submodule.subset_span ⟨sel, φ₀, hD, rfl⟩

end WeldedPath.Supplement.DescriptionCoefficients

end

-- Solutions.WeldedPathCollisionSpectator
section

namespace WeldedPath.ProductDecomposition

open Classical HilbertSupport WeightedCoefficients CoefficientStability
open scoped BigOperators

variable {X Y ι : Type*} [Fintype X] [Fintype Y] [Fintype ι]
  [DecidableEq X] [DecidableEq Y]

theorem linearTensor_row (D : Hil X →ₗ[ℂ] Hil X) (E : Hil Y →ₗ[ℂ] Hil Y)
    (f : Hil (X × Y)) (x : X) :
    row (linearTensor D E f) x = ∑ a, D (ket a) x • E (row f a) := by
  ext y
  change linearTensor D E f (x,y) = _
  rw [linearTensor_apply]
  simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [linear_apply_basis E (row f a) y, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  change f (a,b) * D (ket a) x * E (ket b) y = D (ket a) x * (f (a,b) * E (ket b) y)
  ring

theorem linearTensor_preserves_space (S : Submodule ℂ (Hil X)) (T : Submodule ℂ (Hil Y))
    (D : Hil X →ₗ[ℂ] Hil X) (E : Hil Y →ₗ[ℂ] Hil Y)
    (hD : ∀ f ∈ S, D f ∈ S) (hE : ∀ g ∈ T, E g ∈ T)
    (f : Hil (X × Y)) (hf : f ∈ tensorSpace S T) :
    linearTensor D E f ∈ tensorSpace S T := by
  obtain ⟨hcol,hrow⟩ := (mem_tensorSpace S T f).mp hf
  apply (mem_tensorSpace S T _).mpr
  constructor
  · intro y
    have he : column (linearTensor D E f) y = D (column (rightAction E f) y) := by
      ext x
      exact linearTensor_column D E f x y
    rw [he]
    apply hD
    rw [rightAction_column]
    exact S.sum_mem (fun b _ => S.smul_mem _ (hcol b))
  · intro x
    rw [linearTensor_row]
    exact T.sum_mem (fun a _ => T.smul_mem _ (hE _ (hrow a)))

theorem linearTensor_column_id (D : Hil X →ₗ[ℂ] Hil X)
    (f : Hil (X × Y)) (y : Y) :
    column (linearTensor D (LinearMap.id : Hil Y →ₗ[ℂ] Hil Y) f) y = D (column f y) := by
  have he : rightAction (LinearMap.id : Hil Y →ₗ[ℂ] Hil Y) f = f := by
    ext p
    rfl
  ext x
  change linearTensor D LinearMap.id f (x,y) = D (column f y) x
  rw [linearTensor_column, he]

theorem inner_columns (f g : Hil (X × Y)) :
    inner ℂ f g = ∑ y, inner ℂ (column f y) (column g y) := by
  simp only [PiLp.inner_apply, Fintype.sum_prod_type, column, PiLp.toLp_apply]
  rw [Finset.sum_comm]

theorem norm_columns (f : Hil (X × Y)) : ‖f‖ ^ 2 = ∑ y, ‖column f y‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, column, PiLp.toLp_apply]
  rw [Finset.sum_comm]

theorem column_first_projection (P : X → Prop) (f : Hil (X × Y)) (y : Y) :
    column ((eventSpace (fun p : X × Y => P p.1)).starProjection f) y =
      (eventSpace P).starProjection (column f y) := by
  ext x
  simp [column, eventSpace_projection, diagProj_apply]

theorem projection_leftTensor (P : X → Prop) (D : Hil X →ₗ[ℂ] Hil X)
    (f : Hil (X × Y)) :
    (eventSpace (fun p : X × Y => P p.1)).starProjection
      (linearTensor D (LinearMap.id : Hil Y →ₗ[ℂ] Hil Y) f) =
    linearTensor (((eventSpace P).starProjection.toLinearMap).comp D)
      (LinearMap.id : Hil Y →ₗ[ℂ] Hil Y) f := by
  ext p
  rcases p with ⟨x,y⟩
  change column _ y x = column _ y x
  rw [column_first_projection, linearTensor_column_id, linearTensor_column_id]
  rfl

/-- Add arbitrary spectator components to a linear collision decomposition.
Kernel minimality is used globally, never assumed separately on slices. -/
theorem spectator_collision_bound (S : Submodule ℂ (Hil X)) (T : Submodule ℂ (Hil Y))
    (P : X → Prop) (D : ι → Hil X →ₗ[ℂ] Hil X) (fixed : ι → Prop)
    (hsum : ∀ g ∈ S, (∑ i, D i g) = g)
    (horth : ∀ i j, i ≠ j → ∀ g h, inner ℂ (D i g) (D j h) = 0)
    (hcorth : ∀ i j, i ≠ j → ∀ g h,
      inner ℂ ((eventSpace P).starProjection (D i g))
        ((eventSpace P).starProjection (D j h)) = 0)
    (hfixed : ∀ i, fixed i → ∀ g ∈ S, (eventSpace P).starProjection (D i g) ∈ S)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hfree : ∀ i, ¬fixed i → ∀ g,
      ‖(eventSpace P).starProjection (D i g)‖ ^ 2 ≤ ε * ‖D i g‖ ^ 2)
    (Good : Submodule ℂ (Hil (X × Y)))
    (hbad : eventSpace (fun p : X × Y => P p.1) ≤ Goodᗮ)
    (f : Hil (X × Y)) (hf : f ∈ tensorSpace S T)
    (hminimal : f ∈ (tensorSpace S T ⊓ Goodᗮ)ᗮ) :
    ‖(eventSpace (fun p : X × Y => P p.1)).starProjection f‖ ^ 2 ≤ ε * ‖f‖ ^ 2 := by
  let V : ι → Hil (X × Y) := fun i => linearTensor (D i) LinearMap.id f
  have hsumV : (∑ i, V i) = f := by
    ext p
    rcases p with ⟨x,y⟩
    have hh := congrArg (fun g : Hil X => g x)
      (hsum (column f y) (((mem_tensorSpace S T f).mp hf).1 y))
    change (∑ i, V i) (x,y) = f (x,y)
    simp only [WithLp.ofLp_sum, Finset.sum_apply]
    have hv (i : ι) : V i (x,y) = D i (column f y) x :=
      congrArg (fun z : Hil X => z x) (linearTensor_column_id (D i) f y)
    simp_rw [hv]
    simpa only [WithLp.ofLp_sum, Finset.sum_apply, column, PiLp.toLp_apply] using hh
  have horthV : ∀ i j, i ≠ j → inner ℂ (V i) (V j) = 0 := by
    intro i j hij
    rw [inner_columns]
    simp only [V, linearTensor_column_id]
    exact Finset.sum_eq_zero (fun y _ => horth i j hij _ _)
  apply orthogonal_collision_bound (tensorSpace S T ⊓ Goodᗮ)
    (eventSpace (fun p : X × Y => P p.1)) f hminimal V hsumV ?_ fixed ?_ ε hε ?_ ?_
  · intro i j hij
    rw [inner_columns]
    simp only [column_first_projection, V, linearTensor_column_id]
    exact Finset.sum_eq_zero (fun y _ => hcorth i j hij _ _)
  · intro i hi
    refine ⟨?_, hbad ((eventSpace (fun p : X × Y => P p.1)).starProjection_apply_mem (V i))⟩
    change (eventSpace (fun p : X × Y => P p.1)).starProjection
      (linearTensor (D i) LinearMap.id f) ∈ tensorSpace S T
    rw [projection_leftTensor]
    exact linearTensor_preserves_space S T _ _ (fun g hg => hfixed i hi g hg)
      (fun g hg => hg) f hf
  · intro i hi
    rw [norm_columns, norm_columns, Finset.mul_sum]
    simp only [column_first_projection, V, linearTensor_column_id]
    exact Finset.sum_le_sum (fun y _ => hfree i hi _)
  · rw [← hsumV]
    exact le_of_eq (norm_sum_sq_orthogonal V horthV).symm

end WeldedPath.ProductDecomposition

end

-- Solutions.WeldedPathSectorCollision
section

namespace WeldedPath.CoefficientStability

open scoped BigOperators

variable {E β ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [Fintype β] [Fintype ι]

/-- Cauchy--Schwarz is paid only within a boundary sector. Orthogonal sectors
add in squared norm, so their potentially large number costs nothing. -/
theorem collision_from_sector_decomposition (K C : Submodule ℂ E)
    (T : β → Submodule ℂ E)
    (hT : ∀ b c, b ≠ c → ∀ x ∈ T b, ∀ y ∈ T c, inner ℂ x y = 0)
    (f : E) (hf : f ∈ Kᗮ) (v k r : β → ι → E)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hdec : C.starProjection f = (∑ b, ∑ i, k b i) + ∑ b, ∑ i, r b i)
    (hk : ∀ b i, k b i ∈ K) (hkC : ∀ b i, k b i ∈ C)
    (hrT : ∀ b i, r b i ∈ T b)
    (hr : ∀ b i, ‖r b i‖ ^ 2 ≤ ε * ‖v b i‖ ^ 2)
    (henergy : (∑ b, ∑ i, ‖v b i‖ ^ 2) ≤ ‖f‖ ^ 2) :
    ‖C.starProjection f‖ ^ 2 ≤ (Fintype.card ι : ℝ) * ε * ‖f‖ ^ 2 := by
  have hsT (b : β) : (∑ i, r b i) ∈ T b := (T b).sum_mem (fun i _ => hrT b i)
  calc
    _ ≤ ‖∑ b, ∑ i, r b i‖ ^ 2 := collision_remove_kernel K C f _ _ hf
      (K.sum_mem fun b _ => K.sum_mem fun i _ => hk b i)
      (C.sum_mem fun b _ => C.sum_mem fun i _ => hkC b i) hdec
    _ = ∑ b, ‖∑ i, r b i‖ ^ 2 := norm_sum_sq_orthogonal _
      (fun b c hbc => hT b c hbc _ (hsT b) _ (hsT c))
    _ ≤ ∑ b, (Fintype.card ι : ℝ) * ∑ i, ‖r b i‖ ^ 2 :=
      Finset.sum_le_sum (fun b _ => norm_sum_sq_le_card_sum (r b))
    _ ≤ ∑ b, (Fintype.card ι : ℝ) * (ε * ∑ i, ‖v b i‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro b _
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun i _ => hr b i)
    _ = (Fintype.card ι : ℝ) * ε * (∑ b, ∑ i, ‖v b i‖ ^ 2) := by
      simp only [← mul_assoc, ← Finset.mul_sum]
    _ ≤ (Fintype.card ι : ℝ) * ε * ‖f‖ ^ 2 :=
      mul_le_mul_of_nonneg_left henergy (mul_nonneg (by positivity) hε)

end WeldedPath.CoefficientStability

end

-- Solutions.WeldedPathInternalCollisionSpectator
section

namespace WeldedPath.ProductDecomposition

open Classical HilbertSupport WeightedCoefficients CoefficientStability CollisionStability
open scoped BigOperators

variable {X Y A β ι : Type*} [Fintype X] [Fintype Y] [Fintype β] [Fintype ι]
  [DecidableEq X] [DecidableEq Y] [DecidableEq A]

/-- The within-component collision estimate, grouped by disjoint boundary
patterns and retaining every other component as a constrained spectator. -/
theorem resolved_internal_collision_with_spectator
    (S : Submodule ℂ (Hil X)) (T : Submodule ℂ (Hil Y))
    (D : β × ι → Hil X →ₗ[ℂ] Hil X)
    (μ : β × ι → X → ℝ) (data : β × ι → X → A)
    (hμ : ∀ i x, 0 ≤ μ i x)
    (hlocal : ∀ i, dataSpace (μ i) (data i) ≤ S)
    (hrange : ∀ i g, D i g ∈ dataSpace (μ i) (data i))
    (hsum : ∀ g ∈ S, (∑ i, D i g) = g)
    (horth : ∀ i j, i ≠ j → ∀ g h, inner ℂ (D i g) (D j h) = 0)
    (sector : β → X → Prop)
    (hdis : ∀ b c, b ≠ c → ∀ x, sector b x → ¬sector c x)
    (hsupport : ∀ i g x, ¬sector i.1 x → D i g x = 0)
    (Coin : X → Prop) (Fixed : β × ι → X → Prop) (Q : β × ι → A → Prop)
    (hfixed_data : ∀ i x, Fixed i x ↔ Q i (data i x))
    (hfixed_coin : ∀ i x, Fixed i x → Coin x)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hcap : ∀ i d,
      (∑ x, if data i x = d ∧ (Coin x ∧ ¬Fixed i x) then μ i x else 0) ≤
        ε * ∑ x, if data i x = d then μ i x else 0)
    (Good : Submodule ℂ (Hil (X × Y)))
    (hbad : eventSpace (fun p : X × Y => Coin p.1) ≤ Goodᗮ)
    (f : Hil (X × Y)) (hf : f ∈ tensorSpace S T)
    (hminimal : f ∈ (tensorSpace S T ⊓ Goodᗮ)ᗮ) :
    ‖(eventSpace (fun p : X × Y => Coin p.1)).starProjection f‖ ^ 2 ≤
      (Fintype.card ι : ℝ) * ε * ‖f‖ ^ 2 := by
  let V : β → ι → Hil (X × Y) := fun b i => linearTensor (D (b,i)) LinearMap.id f
  let K : β → ι → Hil (X × Y) := fun b i =>
    (eventSpace (fun p : X × Y => Fixed (b,i) p.1)).starProjection (V b i)
  let R : β → ι → Hil (X × Y) := fun b i =>
    (eventSpace (fun p : X × Y => Coin p.1 ∧ ¬Fixed (b,i) p.1)).starProjection (V b i)
  have hsumV : (∑ b, ∑ i, V b i) = f := by
    ext p
    rcases p with ⟨x,y⟩
    have hh := congrArg (fun g : Hil X => g x)
      (hsum (column f y) (((mem_tensorSpace S T f).mp hf).1 y))
    simp only [WithLp.ofLp_sum, Finset.sum_apply]
    have hv (b : β) (i : ι) : V b i (x,y) = D (b,i) (column f y) x :=
      congrArg (fun z : Hil X => z x) (linearTensor_column_id (D (b,i)) f y)
    simp_rw [hv]
    simpa only [WithLp.ofLp_sum, Finset.sum_apply, Fintype.sum_prod_type,
      column, PiLp.toLp_apply] using hh
  have hVM (b : β) (i : ι) : V b i ∈ eventSpace (fun p : X × Y => sector b p.1) := by
    rintro ⟨x,y⟩ hx
    exact linearTensor_support_left _ _ _ (hsupport (b,i)) f x y hx
  apply collision_from_sector_decomposition (tensorSpace S T ⊓ Goodᗮ)
    (eventSpace (fun p : X × Y => Coin p.1))
    (fun b => eventSpace (fun p : X × Y => sector b p.1))
    ?_ f hminimal V K R ε hε ?_ ?_ ?_ ?_ ?_ ?_
  · intro b c hbc g hg h hh
    rw [PiLp.inner_apply]
    apply Finset.sum_eq_zero
    rintro ⟨x,y⟩ _
    by_cases hb : sector b x
    · rw [hh (x,y) (hdis b c hbc x hb)]
      simp
    · rw [hg (x,y) hb]
      simp
  · rw [← hsumV, map_sum]
    simp only [map_sum]
    calc
      _ = ∑ b, ∑ i, (K b i + R b i) := by
        apply Finset.sum_congr rfl
        intro b _
        apply Finset.sum_congr rfl
        intro i _
        exact event_projection_split (fun p : X × Y => Coin p.1)
          (fun p : X × Y => Fixed (b,i) p.1)
          (fun p hp => hfixed_coin (b,i) p.1 hp) (V b i)
      _ = _ := by simp only [Finset.sum_add_distrib]
  · intro b i
    have hm : ∀ g ∈ S, (eventSpace (Fixed (b,i))).starProjection (D (b,i) g) ∈ S := by
      intro g _
      apply hlocal (b,i)
      exact masked_mem_dataSpace_of_support _ _ _ (Q (b,i)) _ (hrange (b,i) g)
        (fun x _ => hfixed_data (b,i) x)
    have hkS : K b i ∈ tensorSpace S T := by
      change (eventSpace (fun p : X × Y => Fixed (b,i) p.1)).starProjection
        (linearTensor (D (b,i)) LinearMap.id f) ∈ tensorSpace S T
      rw [projection_leftTensor]
      exact linearTensor_preserves_space S T _ _ hm (fun g hg => hg) f hf
    have hkC : K b i ∈ eventSpace (fun p : X × Y => Coin p.1) := by
      apply eventSpace_mono (fun p : X × Y => Fixed (b,i) p.1)
        (fun p : X × Y => Coin p.1) (fun p hp => hfixed_coin (b,i) p.1 hp)
      exact (eventSpace (fun p : X × Y => Fixed (b,i) p.1)).starProjection_apply_mem (V b i)
    exact ⟨hkS, hbad hkC⟩
  · intro b i
    apply eventSpace_mono (fun p : X × Y => Fixed (b,i) p.1)
      (fun p : X × Y => Coin p.1) (fun p hp => hfixed_coin (b,i) p.1 hp)
    exact (eventSpace (fun p : X × Y => Fixed (b,i) p.1)).starProjection_apply_mem (V b i)
  · intro b i p hp
    change ((eventSpace (fun p : X × Y => Coin p.1 ∧ ¬Fixed (b,i) p.1)).starProjection
      (V b i)) p = 0
    simp [eventSpace_projection, diagProj_apply, hVM b i p hp]
  · intro b i
    rw [norm_columns, norm_columns, Finset.mul_sum]
    simp only [R, V]
    apply Finset.sum_le_sum
    intro y _
    rw [column_first_projection (fun x => Coin x ∧ ¬Fixed (b,i) x),
      linearTensor_column_id]
    obtain ⟨h, hh⟩ := (mem_dataSpace (μ (b,i)) (data (b,i)) _).mp
      (hrange (b,i) (column f y))
    rw [← hh]
    exact conditional_event_bound (μ (b,i)) (hμ (b,i)) (data (b,i))
      (fun x => Coin x ∧ ¬Fixed (b,i) x) ε (hcap (b,i)) h
  · have ho : ∀ i j : β × ι, i ≠ j → inner ℂ (V i.1 i.2) (V j.1 j.2) = 0 := by
      intro i j hij
      rw [inner_columns]
      simp only [V, linearTensor_column_id]
      exact Finset.sum_eq_zero (fun y _ => horth i j hij _ _)
    have he := norm_sum_sq_orthogonal (fun i : β × ι => V i.1 i.2) ho
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type, hsumV] at he
    exact he.symm.le

end WeldedPath.ProductDecomposition

end

-- Solutions.WeldedPathEdgeCoefficientWeightedSplit
section

namespace WeldedPath.Supplement.EdgeCoefficientSplit

open scoped BigOperators
open Classical FixedDataFunctions
open WeldedPath.WeightedCoefficients

variable {n : ℕ}

/-- The same centered residual works after arbitrary diagonal weighting by
the root's fixed data. The two sides may even use different root functions. -/
theorem edge_split_weighted (l : ℕ) (G : WeldedInstance n) (hG : G.IsValid)
    (H : AbsForest n) (hH : H.IsValid) (allowed : Fin H.k → Label n → Prop)
    (e : Fin H.k × Fin H.k) (he : e ∈ H.E) (c p : Fin H.k)
    (hends : e = (c, p) ∨ e = (p, c)) (P : Fin H.k → Prop) [DecidablePred P]
    (hc : P c) (hp : ¬P p)
    (hcut : ∀ q ∈ H.E, q ≠ e → (P q.1 ↔ P q.2)) (h : Data H → ℂ) :
    ∃ r t : Data H → ℂ,
      (∀ φ : Fin H.k → Label n,
        h (H.Wfix φ c) = r (H.Wfix φ c) + t (H.Wfix φ p)) ∧
      (∀ φ : Fin H.k → Label n, ¬H.IsWeldUnder φ e → r (H.Wfix φ c) = 0) ∧
      (∀ a : Fin H.k, ¬P a → ∀ v : Fin H.k, ¬P v →
        ∀ m₁ m₂ k : Data H → ℂ,
        inner ℂ
          (lift (maskedReference l G H allowed)
            (fun φ => m₁ (H.Wfix φ a) * k (H.Wfix φ v)))
          (lift (maskedReference l G H allowed)
            (fun φ => m₂ (H.Wfix φ a) * r (H.Wfix φ c))) = 0) := by
  obtain ⟨r, t, hsum, hsupp, horth⟩ :=
    edge_split_measurable l G hG H hH allowed e he c p hends P hc hp hcut h
  refine ⟨r, t, hsum, hsupp, ?_⟩
  intro a ha v hv m₁ m₂ k
  let M : Data H → ℂ := fun d => m₁ d * star (m₂ d)
  let K : (Fin H.k → Label n) → ℂ := fun φ => M (H.Wfix φ a) * k (H.Wfix φ v)
  obtain ⟨gM, hgM⟩ := weld_local_representation H hH e p c hends.symm (fun u => ¬P u)
    hp (fun q hq hqe => not_congr (hcut q hq hqe)) a ha M
  obtain ⟨gk, hgk⟩ := weld_local_representation H hH e p c hends.symm (fun u => ¬P u)
    hp (fun q hq hqe => not_congr (hcut q hq hqe)) v hv k
  have hrepr (φ : Fin H.k → Label n) :
      (if H.IsWeldUnder φ e then K φ else 0) =
        gM (φ c) (fun b => φ b) * gk (φ c) (fun b => φ b) := by
    rw [← hgM φ, ← hgk φ]
    by_cases hw : H.IsWeldUnder φ e
    · simp only [hw, ite_true, K]
    · simp only [hw, ite_false, mul_zero]
  have hK : Function.FactorsThrough
      (fun φ => if H.IsWeldUnder φ e then K φ else 0)
      (fun φ => (φ c, fun b : {b // ¬P b} => φ b)) := by
    intro φ ψ hd
    dsimp only at hd ⊢
    rw [hrepr φ, hrepr ψ]
    exact congrArg (fun q => gM q.1 q.2 * gk q.1 q.2) hd
  have hz := horth K hK
  calc
    _ = inner ℂ
        (lift (maskedReference l G H allowed) K)
        (lift (maskedReference l G H allowed) (fun φ => r (H.Wfix φ c))) := by
      rw [inner_lift _ (maskedReference_nonneg l G H hH allowed),
        inner_lift _ (maskedReference_nonneg l G H hH allowed)]
      apply Finset.sum_congr rfl
      intro φ _
      dsimp only [K, M]
      simp only [star_mul, star_star]
      ring
    _ = 0 := hz

end WeldedPath.Supplement.EdgeCoefficientSplit

end

-- Solutions.WeldedPathWeightedPeeling
section

namespace WeldedPath.CoefficientStability

open scoped BigOperators

variable {E Θ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- Uniformly centered peeling yields one decomposition which is orthogonal
and energy-preserving for every linear weighting in the specified family. -/
theorem weighted_peeling_of_splits (A : ℕ → Submodule ℂ E) (T : Θ → E →ₗ[ℂ] E)
    (hsplit : ∀ i x, x ∈ A i → ∃ r, r ∈ A i ∧ x - r ∈ initialSpace A i ∧
      ∀ θ y, y ∈ initialSpace A i → inner ℂ (T θ y) (T θ r) = 0)
    (m : ℕ) (f : E) (hf : f ∈ initialSpace A m) :
    ∃ v : ℕ → E, (∀ i < m, v i ∈ A i) ∧
      (∑ i ∈ Finset.range m, v i) = f ∧
      (∀ θ i j, i < j → j < m → inner ℂ (T θ (v i)) (T θ (v j)) = 0) ∧
      (∀ θ, (∑ i ∈ Finset.range m, ‖T θ (v i)‖ ^ 2) = ‖T θ f‖ ^ 2) := by
  classical
  induction m generalizing f with
  | zero =>
    have hf0 : f = 0 := hf
    subst f
    exact ⟨fun _ => 0, by simp, by simp, by simp, by simp⟩
  | succ m ih =>
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp hf
    obtain ⟨r, hr, hmean, horth⟩ := hsplit m y hy
    let p := x + (y - r)
    have hp : p ∈ initialSpace A m := (initialSpace A m).add_mem hx hmean
    have hpr : p + r = f := by dsimp [p]; rw [← hxy]; abel
    obtain ⟨v, hv, hvs, hvp, hve⟩ := ih p hp
    let w : ℕ → E := fun i => if i = m then r else v i
    have hwi : ∀ i ∈ Finset.range m, w i = v i := by
      intro i hi
      exact if_neg (Nat.ne_of_lt (Finset.mem_range.mp hi))
    have hws : (∑ i ∈ Finset.range m, w i) = p := by
      rw [Finset.sum_congr rfl hwi, hvs]
    refine ⟨w, ?_, ?_, ?_, ?_⟩
    · intro i hi
      by_cases him : i = m
      · subst i
        simpa only [w, if_pos rfl] using hr
      · simpa only [w, if_neg him] using hv i (by omega)
    · rw [Finset.sum_range_succ, hws]
      simpa only [w, if_pos rfl] using hpr
    · intro θ i j hij hj
      by_cases hjm : j = m
      · subst j
        have him : i ≠ m := Nat.ne_of_lt hij
        simp only [w, if_neg him, if_pos rfl]
        exact horth θ (v i) ((le_prefix A hij) (hv i hij))
      · have hjm' : j < m := by omega
        have him : i ≠ m := by omega
        simp only [w, if_neg him, if_neg hjm]
        exact hvp θ i j hij hjm'
    · intro θ
      have hwe : (∑ i ∈ Finset.range m, ‖T θ (w i)‖ ^ 2) = ‖T θ p‖ ^ 2 := by
        rw [← hve θ]
        exact Finset.sum_congr rfl
          (fun i hi => congrArg (fun z : E => ‖T θ z‖ ^ 2) (hwi i hi))
      rw [Finset.sum_range_succ, hwe]
      have he := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
        (T θ p) (T θ r) (horth θ p hp)
      have heq : T θ p + T θ r = T θ f := by rw [← map_add, hpr]
      rw [heq] at he
      simpa only [w, if_pos rfl, pow_two] using he.symm

/-- Orthogonality to every local space extends to their initial span after
applying the same linear weighting to both arguments. -/
theorem weighted_orthogonal_to_initial (A : ℕ → Submodule ℂ E) (T : E →ₗ[ℂ] E)
    (m : ℕ) (r : E) (h : ∀ i < m, ∀ x ∈ A i, inner ℂ (T x) (T r) = 0) :
    ∀ x ∈ initialSpace A m, inner ℂ (T x) (T r) = 0 := by
  induction m with
  | zero => intro x hx; have hx0 : x = 0 := hx; simp [hx0]
  | succ m ih =>
    intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add, inner_add_left, ih (fun i hi => h i (by omega)) y hy,
      h m (Nat.lt_succ_self _) z hz, add_zero]

end WeldedPath.CoefficientStability

end

-- Solutions.WeldedPathWeightedDecomposition
section

namespace WeldedPath.Supplement.CoefficientDecomposition

open Classical CoefficientOrder EdgeCoefficientSplit FixedDataFunctions
open WeldedPath.WeightedCoefficients WeldedPath.CoefficientStability
open scoped BigOperators

variable {n : ℕ}

noncomputable def rootMultiplier (H : AbsForest n) (s : Fin H.k) (m : Data H → ℂ) :
    Hil (Fin H.k → Label n) →ₗ[ℂ] Hil (Fin H.k → Label n) where
  toFun f := WithLp.toLp 2 (fun φ => m (H.Wfix φ s) * f φ)
  map_add' f g := by
    ext φ
    change m (H.Wfix φ s) * (f φ + g φ) = m (H.Wfix φ s) * f φ + m (H.Wfix φ s) * g φ
    ring
  map_smul' c f := by
    ext φ
    change m (H.Wfix φ s) * (c * f φ) = c * (m (H.Wfix φ s) * f φ)
    ring

theorem rootMultiplier_lift (H : AbsForest n) (s : Fin H.k) (m : Data H → ℂ)
    (μ : (Fin H.k → Label n) → ℝ) (f : (Fin H.k → Label n) → ℂ) :
    rootMultiplier H s m (lift μ f) = lift μ (fun φ => m (H.Wfix φ s) * f φ) := by
  ext φ
  change m (H.Wfix φ s) * ((Real.sqrt (μ φ) : ℂ) * f φ) =
    (Real.sqrt (μ φ) : ℂ) * (m (H.Wfix φ s) * f φ)
  ring

/-- One actual rooted decomposition is orthogonal and energy-preserving
after multiplication by every function of the root's fixed data. -/
theorem rooted_weighted_decomposition (l : ℕ) (G : WeldedInstance n) (hG : G.IsValid)
    (H : AbsForest n) (hH : H.IsValid) (s : Fin H.k)
    (hconn : ∀ u, H.graph.Reachable s u) (allowed : Fin H.k → Label n → Prop)
    (f : Hil (Fin H.k → Label n))
    (hf : f ∈ ⨆ v, localCoefficientSpace H (maskedReference l G H allowed) v) :
    ∃ g : Fin H.k → Hil (Fin H.k → Label n),
      (∀ v, g v ∈ localCoefficientSpace H (maskedReference l G H allowed) v) ∧
      (∑ v, g v) = f ∧
      (∀ m : Data H → ℂ, ∀ u v, u ≠ v →
        inner ℂ (rootMultiplier H s m (g u)) (rootMultiplier H s m (g v)) = 0) ∧
      (∀ m : Data H → ℂ,
        (∑ v, ‖rootMultiplier H s m (g v)‖ ^ 2) = ‖rootMultiplier H s m f‖ ^ 2) := by
  let μ := maskedReference l G H allowed
  obtain ⟨order, hord, hroot⟩ := exists_root_order H s hconn
  let A : ℕ → Submodule ℂ (Hil (Fin H.k → Label n)) :=
    fun i => if hi : i < H.k then localCoefficientSpace H μ (order ⟨i, hi⟩) else ⊥
  have hA (i : Fin H.k) : A i.val = localCoefficientSpace H μ (order i) := by
    simp only [A, dif_pos i.isLt]
  have hsplit : ∀ i x, x ∈ A i → ∃ r, r ∈ A i ∧ x - r ∈ initialSpace A i ∧
      ∀ m y, y ∈ initialSpace A i →
        inner ℂ (rootMultiplier H s m y) (rootMultiplier H s m r) = 0 := by
    intro i x hx
    by_cases hi : i < H.k
    · let ii : Fin H.k := ⟨i, hi⟩
      by_cases hr : order ii = s
      · have he : ii = ⟨0, by have := s.isLt; omega⟩ := order.injective (hr.trans hroot.symm)
        have hi0 : i = 0 := congrArg Fin.val he
        subst i
        refine ⟨x, hx, by simp, ?_⟩
        intro m y hy
        have hy0 : y = 0 := hy
        simp [hy0]
      · obtain ⟨j, hji, e, he, hends, P, hc, hp, hcut, hearlier⟩ :=
          earlier_parent_and_cut H hH s hconn order hord ii hr
        have hiPos : 0 < i := by
          by_contra hn
          have hi0 : i = 0 := by omega
          have he : ii = ⟨0, by have := s.isLt; omega⟩ := Fin.ext hi0
          apply hr
          simpa only [he] using hroot
        have hsout : ¬P s := by
          have hout := hearlier ⟨0, by have := s.isLt; omega⟩ hiPos
          simpa only [hroot] using hout
        have hx' : x ∈ localCoefficientSpace H μ (order ii) := by rwa [hA ii] at hx
        obtain ⟨h, hh⟩ : ∃ h : Data H → ℂ,
            lift μ (fun φ => h (H.Wfix φ (order ii))) = x :=
          (mem_dataSpace μ (fun φ => H.Wfix φ (order ii)) x).mp hx'
        obtain ⟨r, t, hdec, _, horth⟩ :=
          edge_split_weighted l G hG H hH allowed e he (order ii) (order j) hends P hc hp hcut h
        let rv := lift μ (fun φ => r (H.Wfix φ (order ii)))
        let tv := lift μ (fun φ => t (H.Wfix φ (order j)))
        have heq : x = rv + tv := by
          rw [← hh]
          ext φ
          change (Real.sqrt (μ φ) : ℂ) * h (H.Wfix φ (order ii)) =
            (Real.sqrt (μ φ) : ℂ) * r (H.Wfix φ (order ii)) +
            (Real.sqrt (μ φ) : ℂ) * t (H.Wfix φ (order j))
          rw [hdec φ, mul_add]
        refine ⟨rv, ?_, ?_, ?_⟩
        · rw [hA ii]
          exact lift_mem_dataSpace μ (fun φ => H.Wfix φ (order ii)) r
        · have ht : tv ∈ A j.val := by
            rw [hA j]
            exact lift_mem_dataSpace μ (fun φ => H.Wfix φ (order j)) t
          have hs : x - rv = tv := by rw [heq]; abel
          rw [hs]
          exact (le_prefix A hji) ht
        · intro m y hy
          apply weighted_orthogonal_to_initial A (rootMultiplier H s m) i rv ?_ y hy
          intro a hai z hz
          have ha : a < H.k := lt_trans hai hi
          let aa : Fin H.k := ⟨a, ha⟩
          have hz' : z ∈ localCoefficientSpace H μ (order aa) := by rwa [hA aa] at hz
          obtain ⟨k, hk⟩ := (mem_dataSpace μ (fun φ => H.Wfix φ (order aa)) z).mp hz'
          rw [← hk]
          simpa only [rv, rootMultiplier_lift, Function.comp_apply, μ] using
            horth s hsout (order aa) (hearlier aa hai) m m k
    · have hx0 : x = 0 := by simpa only [A, dif_neg hi, Submodule.mem_bot] using hx
      subst x
      exact ⟨0, by simp, by simp, by simp⟩
  have hsup : (⨆ v, localCoefficientSpace H μ v) ≤ initialSpace A H.k := by
    apply iSup_le
    intro v
    have h := le_prefix A (order.symm v).isLt
    rw [hA (order.symm v), Equiv.apply_symm_apply] at h
    exact h
  obtain ⟨v, hv, hvs, hvp, hve⟩ :=
    weighted_peeling_of_splits A (rootMultiplier H s) hsplit H.k f (hsup hf)
  let g : Fin H.k → Hil (Fin H.k → Label n) := fun u => v (order.symm u).val
  refine ⟨g, ?_, ?_, ?_, ?_⟩
  · intro u
    have h := hv (order.symm u).val (order.symm u).isLt
    rwa [hA (order.symm u), Equiv.apply_symm_apply] at h
  · change (∑ u, v (order.symm u).val) = f
    rw [Equiv.sum_comp order.symm (fun i : Fin H.k => v i.val), Fin.sum_univ_eq_sum_range]
    exact hvs
  · intro m u w huw
    have hne : (order.symm u).val ≠ (order.symm w).val := by
      intro he
      exact huw (order.symm.injective (Fin.ext he))
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact hvp m _ _ hlt (order.symm w).isLt
    · exact inner_eq_zero_symm.mpr (hvp m _ _ hgt (order.symm u).isLt)
  · intro m
    change (∑ u, ‖rootMultiplier H s m (v (order.symm u).val)‖ ^ 2) = _
    rw [Equiv.sum_comp order.symm (fun i : Fin H.k => ‖rootMultiplier H s m (v i.val)‖ ^ 2),
      Fin.sum_univ_eq_sum_range (fun i : ℕ => ‖rootMultiplier H s m (v i)‖ ^ 2)]
    exact hve m

end WeldedPath.Supplement.CoefficientDecomposition

end

-- Solutions.WeldedPathLinearPeeling
section

namespace WeldedPath.CoefficientStability

open scoped BigOperators

variable {E Θ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

noncomputable def residualSpace (A : ℕ → Submodule ℂ E) (i : ℕ) : Submodule ℂ E :=
  A i ⊓ (initialSpace A i)ᗮ

theorem residual_orthogonal {A : ℕ → Submodule ℂ E} {i j : ℕ} (hij : i < j)
    {x y : E} (hx : x ∈ residualSpace A i) (hy : y ∈ residualSpace A j) :
    inner ℂ x y = 0 :=
  ((initialSpace A j).mem_orthogonal y).mp hy.2 x ((le_prefix A hij) hx.1)

theorem residual_projection_sum (A : ℕ → Submodule ℂ E)
    (hsplit : ∀ i x, x ∈ A i → ∃ r, r ∈ residualSpace A i ∧
      x - r ∈ initialSpace A i)
    (m : ℕ) (f : E) (hf : f ∈ initialSpace A m) :
    (∑ i ∈ Finset.range m, (residualSpace A i).starProjection f) = f := by
  classical
  induction m generalizing f with
  | zero =>
    have hf0 : f = 0 := hf
    simp [hf0]
  | succ m ih =>
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp hf
    obtain ⟨r, hr, hmean⟩ := hsplit m y hy
    let p := x + (y - r)
    have hp : p ∈ initialSpace A m := (initialSpace A m).add_mem hx hmean
    have hpr : p + r = f := by dsimp [p]; rw [← hxy]; abel
    have hearly : ∀ i ∈ Finset.range m,
        (residualSpace A i).starProjection f = (residualSpace A i).starProjection p := by
      intro i hi
      rw [← hpr, map_add]
      have hz : (residualSpace A i).starProjection r = 0 := by
        apply (residualSpace A i).starProjection_apply_eq_zero_iff.mpr
        intro z hz
        exact residual_orthogonal (Finset.mem_range.mp hi) hz hr
      rw [hz, add_zero]
    have hlast : (residualSpace A m).starProjection f = r := by
      rw [← hpr, map_add, (residualSpace A m).starProjection_eq_self_iff.mpr hr]
      have hz : (residualSpace A m).starProjection p = 0 := by
        apply (residualSpace A m).starProjection_apply_eq_zero_iff.mpr
        intro z hz
        exact inner_eq_zero_symm.mpr (((initialSpace A m).mem_orthogonal z).mp hz.2 p hp)
      rw [hz, zero_add]
    rw [Finset.sum_range_succ, Finset.sum_congr rfl hearly, ih p hp, hlast, hpr]

/-- A uniform weighted centering identity extends from the chosen residuals
to the entire fixed residual subspace. Thus it holds across different inputs. -/
theorem residual_weighted_orthogonal (A : ℕ → Submodule ℂ E)
    (T : Θ → E →ₗ[ℂ] E)
    (hsplit : ∀ i x, x ∈ A i → ∃ r, r ∈ residualSpace A i ∧
      x - r ∈ initialSpace A i ∧
      ∀ θ y, y ∈ initialSpace A i → inner ℂ (T θ y) (T θ r) = 0)
    {i j : ℕ} (hij : i < j) {x y : E}
    (hx : x ∈ residualSpace A i) (hy : y ∈ residualSpace A j) (θ : Θ) :
    inner ℂ (T θ x) (T θ y) = 0 := by
  obtain ⟨r, hr, hmean, horth⟩ := hsplit j y hy.1
  have hzero : y - r = 0 := by
    have hmem : y - r ∈ (initialSpace A j)ᗮ :=
      (initialSpace A j)ᗮ.sub_mem hy.2 hr.2
    exact inner_self_eq_zero.mp (((initialSpace A j).mem_orthogonal (y-r)).mp
      hmem (y-r) hmean)
  have hyr : y = r := sub_eq_zero.mp hzero
  rw [hyr]
  exact horth θ x ((le_prefix A hij) hx.1)

/-- Canonical linear projections implement the centered peeling. The maps
work simultaneously for all inputs, and have weighted cross-orthogonal ranges. -/
theorem linear_weighted_peeling (A : ℕ → Submodule ℂ E) (T : Θ → E →ₗ[ℂ] E)
    (hsplit : ∀ i x, x ∈ A i → ∃ r, r ∈ residualSpace A i ∧
      x - r ∈ initialSpace A i ∧
      ∀ θ y, y ∈ initialSpace A i → inner ℂ (T θ y) (T θ r) = 0)
    (m : ℕ) :
    ∃ D : Fin m → E →ₗ[ℂ] E,
      (∀ i f, D i f ∈ residualSpace A i.val) ∧
      (∀ f ∈ initialSpace A m, (∑ i, D i f) = f) ∧
      (∀ θ i j, i ≠ j → ∀ f g,
        inner ℂ (T θ (D i f)) (T θ (D j g)) = 0) := by
  classical
  let D : Fin m → E →ₗ[ℂ] E := fun i => (residualSpace A i.val).starProjection.toLinearMap
  refine ⟨D, ?_, ?_, ?_⟩
  · intro i f
    exact (residualSpace A i.val).starProjection_apply_mem f
  · intro f hf
    change (∑ i : Fin m, (residualSpace A i.val).starProjection f) = f
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => (residualSpace A i).starProjection f)]
    exact residual_projection_sum A (fun i x hx => by
      obtain ⟨r, hr, hm, _⟩ := hsplit i x hx
      exact ⟨r, hr, hm⟩) m f hf
  · intro θ i j hij f g
    have hne : i.val ≠ j.val := fun he => hij (Fin.ext he)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact residual_weighted_orthogonal A T hsplit hlt
        ((residualSpace A i.val).starProjection_apply_mem f)
        ((residualSpace A j.val).starProjection_apply_mem g) θ
    · exact inner_eq_zero_symm.mpr (residual_weighted_orthogonal A T hsplit hgt
        ((residualSpace A j.val).starProjection_apply_mem g)
        ((residualSpace A i.val).starProjection_apply_mem f) θ)

end WeldedPath.CoefficientStability

end

-- Solutions.WeldedPathLinearDecomposition
section

namespace WeldedPath.Supplement.CoefficientDecomposition

open Classical CoefficientOrder EdgeCoefficientSplit FixedDataFunctions
open WeldedPath.WeightedCoefficients WeldedPath.CoefficientStability
open scoped BigOperators

variable {n : ℕ}

@[simp] theorem rootMultiplier_one (H : AbsForest n) (s : Fin H.k)
    (f : Hil (Fin H.k → Label n)) : rootMultiplier H s (fun _ => 1) f = f := by
  ext φ
  change 1 * f φ = f φ
  exact one_mul _

/-- Fixed linear maps, independent of the input coefficient, implement the
rooted decomposition. Their ranges are orthogonal even across different
inputs after arbitrary root-data weighting. -/
theorem rooted_linear_decomposition (l : ℕ) (G : WeldedInstance n) (hG : G.IsValid)
    (H : AbsForest n) (hH : H.IsValid) (s : Fin H.k)
    (hconn : ∀ u, H.graph.Reachable s u) (allowed : Fin H.k → Label n → Prop) :
    ∃ D : Fin H.k → Hil (Fin H.k → Label n) →ₗ[ℂ] Hil (Fin H.k → Label n),
      (∀ v f, D v f ∈ localCoefficientSpace H (maskedReference l G H allowed) v) ∧
      (∀ f ∈ ⨆ v, localCoefficientSpace H (maskedReference l G H allowed) v,
        (∑ v, D v f) = f) ∧
      (∀ m : Data H → ℂ, ∀ u v, u ≠ v → ∀ f g,
        inner ℂ (rootMultiplier H s m (D u f)) (rootMultiplier H s m (D v g)) = 0) ∧
      (∀ v f φ, (D v f) φ ≠ 0 →
        v = s ∨ H.graph.Adj s v ∨ s ∉ H.Sfix φ v) := by
  let μ := maskedReference l G H allowed
  obtain ⟨order, hord, hroot⟩ := exists_root_order H s hconn
  let A : ℕ → Submodule ℂ (Hil (Fin H.k → Label n)) :=
    fun i => if hi : i < H.k then localCoefficientSpace H μ (order ⟨i, hi⟩) else ⊥
  have hA (i : Fin H.k) : A i.val = localCoefficientSpace H μ (order i) := by
    simp only [A, dif_pos i.isLt]
  let Q : ℕ → Submodule ℂ (Hil (Fin H.k → Label n)) := fun i =>
    if hi : i < H.k then eventSpace (fun φ =>
      order ⟨i, hi⟩ = s ∨ H.graph.Adj s (order ⟨i, hi⟩) ∨
        s ∉ H.Sfix φ (order ⟨i, hi⟩)) else ⊥
  have hsplit : ∀ i x, x ∈ A i → ∃ r, r ∈ A i ∧ x - r ∈ initialSpace A i ∧
      (∀ m y, y ∈ initialSpace A i →
        inner ℂ (rootMultiplier H s m y) (rootMultiplier H s m r) = 0) ∧ r ∈ Q i := by
    intro i x hx
    by_cases hi : i < H.k
    · let ii : Fin H.k := ⟨i, hi⟩
      by_cases hr : order ii = s
      · have he : ii = ⟨0, by have := s.isLt; omega⟩ := order.injective (hr.trans hroot.symm)
        have hi0 : i = 0 := congrArg Fin.val he
        subst i
        refine ⟨x, hx, by simp, ?_, ?_⟩
        · intro m y hy
          have hy0 : y = 0 := hy
          simp [hy0]
        · dsimp only [Q]
          rw [dif_pos hi]
          change x ∈ eventSpace (fun φ => order ⟨0, hi⟩ = s ∨ _)
          intro φ hφ
          exact (hφ (Or.inl hroot)).elim
      · obtain ⟨j, hji, e, he, hends, P, hc, hp, hcut, hearlier⟩ :=
          earlier_parent_and_cut H hH s hconn order hord ii hr
        have hiPos : 0 < i := by
          by_contra hn
          have hi0 : i = 0 := by omega
          have he : ii = ⟨0, by have := s.isLt; omega⟩ := Fin.ext hi0
          apply hr
          simpa only [he] using hroot
        have hsout : ¬P s := by
          have hout := hearlier ⟨0, by have := s.isLt; omega⟩ hiPos
          simpa only [hroot] using hout
        have hx' : x ∈ localCoefficientSpace H μ (order ii) := by rwa [hA ii] at hx
        obtain ⟨h, hh⟩ : ∃ h : Data H → ℂ,
            lift μ (fun φ => h (H.Wfix φ (order ii))) = x :=
          (mem_dataSpace μ (fun φ => H.Wfix φ (order ii)) x).mp hx'
        obtain ⟨r, t, hdec, hzero, horth⟩ :=
          edge_split_weighted l G hG H hH allowed e he (order ii) (order j) hends P hc hp hcut h
        let rv := lift μ (fun φ => r (H.Wfix φ (order ii)))
        let tv := lift μ (fun φ => t (H.Wfix φ (order j)))
        have heq : x = rv + tv := by
          rw [← hh]
          ext φ
          change (Real.sqrt (μ φ) : ℂ) * h (H.Wfix φ (order ii)) =
            (Real.sqrt (μ φ) : ℂ) * r (H.Wfix φ (order ii)) +
            (Real.sqrt (μ φ) : ℂ) * t (H.Wfix φ (order j))
          rw [hdec φ, mul_add]
        refine ⟨rv, ?_, ?_, ?_, ?_⟩
        · rw [hA ii]
          exact lift_mem_dataSpace μ (fun φ => H.Wfix φ (order ii)) r
        · have ht : tv ∈ A j.val := by
            rw [hA j]
            exact lift_mem_dataSpace μ (fun φ => H.Wfix φ (order j)) t
          have hs : x - rv = tv := by rw [heq]; abel
          rw [hs]
          exact (le_prefix A hji) ht
        · intro m y hy
          apply weighted_orthogonal_to_initial A (rootMultiplier H s m) i rv ?_ y hy
          intro a hai z hz
          have ha : a < H.k := lt_trans hai hi
          let aa : Fin H.k := ⟨a, ha⟩
          have hz' : z ∈ localCoefficientSpace H μ (order aa) := by rwa [hA aa] at hz
          obtain ⟨k, hk⟩ := (mem_dataSpace μ (fun φ => H.Wfix φ (order aa)) z).mp hz'
          rw [← hk]
          simpa only [rv, rootMultiplier_lift, Function.comp_apply, μ] using
            horth s hsout (order aa) (hearlier aa hai) m m k
        · dsimp only [Q]
          rw [dif_pos hi]
          change rv ∈ eventSpace (fun φ => order ii = s ∨ H.graph.Adj s (order ii) ∨
            s ∉ H.Sfix φ (order ii))
          intro φ hφ
          by_cases hw : H.IsWeldUnder φ e
          · have hsfix : s ∈ H.Sfix φ (order ii) := by tauto
            have hout := FixedDataSeparator.sfix_on_side_or_endpoints H φ e P hcut hw
              (order ii) hc s hsfix
            rcases hout with hh | hh | hh
            · exact (hsout hh).elim
            · have hadj : H.graph.Adj s (order ii) := by
                rcases hends with heq | heq
                · have hsc : s = order ii := by simpa only [heq] using hh
                  exact (hr hsc.symm).elim
                · have hsp : s = order j := by simpa only [heq] using hh
                  subst s
                  exact ⟨by simpa only [heq] using ne_of_lt (hH.1 e he),
                    Or.inl (by simpa only [heq] using he)⟩
              exact (hφ (Or.inr (Or.inl hadj))).elim
            · have hadj : H.graph.Adj s (order ii) := by
                rcases hends with heq | heq
                · have hsp : s = order j := by simpa only [heq] using hh
                  subst s
                  exact ⟨by simpa only [heq] using (ne_of_lt (hH.1 e he)).symm,
                    Or.inr (by simpa only [heq] using he)⟩
                · have hsc : s = order ii := by simpa only [heq] using hh
                  exact (hr hsc.symm).elim
              exact (hφ (Or.inr (Or.inl hadj))).elim
          · change (Real.sqrt (μ φ) : ℂ) * r (H.Wfix φ (order ii)) = 0
            rw [hzero φ hw, mul_zero]
    · have hx0 : x = 0 := by simpa only [A, dif_neg hi, Submodule.mem_bot] using hx
      subst x
      exact ⟨0, by simp, by simp, by simp, (Q i).zero_mem⟩
  have hsup : (⨆ v, localCoefficientSpace H μ v) ≤ initialSpace A H.k := by
    apply iSup_le
    intro v
    have h := le_prefix A (order.symm v).isLt
    rw [hA (order.symm v), Equiv.apply_symm_apply] at h
    exact h
  have hsplit' : ∀ i x, x ∈ A i → ∃ r, r ∈ residualSpace A i ∧
      x - r ∈ initialSpace A i ∧ ∀ m y, y ∈ initialSpace A i →
        inner ℂ (rootMultiplier H s m y) (rootMultiplier H s m r) = 0 := by
    intro i x hx
    obtain ⟨r, hr, hm, ho, _⟩ := hsplit i x hx
    refine ⟨r, ⟨hr, ?_⟩, hm, ho⟩
    intro y hy
    simpa only [rootMultiplier_one] using ho (fun _ => 1) y hy
  obtain ⟨D, hD, hsum, horth⟩ := linear_weighted_peeling A (rootMultiplier H s) hsplit' H.k
  let R := fun v : Fin H.k => D (order.symm v)
  refine ⟨R, ?_, ?_, ?_, ?_⟩
  · intro v f
    have hh := (hD (order.symm v) f).1
    rwa [hA (order.symm v), Equiv.apply_symm_apply] at hh
  · intro f hf
    change (∑ v, D (order.symm v) f) = f
    rw [Equiv.sum_comp order.symm (fun i => D i f)]
    exact hsum f (hsup hf)
  · intro m u v huv f g
    exact horth m (order.symm u) (order.symm v)
      (fun he => huv (order.symm.injective he)) f g
  · intro v f φ hne
    let i := order.symm v
    have hv := hD i f
    obtain ⟨r, hr, hm, ho, hQ⟩ := hsplit i.val (D i f) hv.1
    have hro : r ∈ (initialSpace A i.val)ᗮ := by
      intro y hy
      simpa only [rootMultiplier_one] using ho (fun _ => 1) y hy
    have heq : D i f = r := by
      apply sub_eq_zero.mp
      have hh := (initialSpace A i.val)ᗮ.sub_mem hv.2 hro
      exact inner_self_eq_zero.mp (((initialSpace A i.val).mem_orthogonal _).mp hh _ hm)
    have hq : D i f ∈ Q i.val := heq.symm ▸ hQ
    dsimp only [Q] at hq
    rw [dif_pos i.isLt] at hq
    change D i f ∈ eventSpace (fun ψ => order i = s ∨ H.graph.Adj s (order i) ∨
      s ∉ H.Sfix ψ (order i)) at hq
    have hp : order i = s ∨ H.graph.Adj s (order i) ∨ s ∉ H.Sfix φ (order i) := by
      by_contra hn
      exact hne (hq φ hn)
    simpa only [i, Equiv.apply_symm_apply] using hp

end WeldedPath.Supplement.CoefficientDecomposition

end

-- Solutions.WeldedPathAnchoredLinearSplit
section

namespace WeldedPath.Supplement.AnchoredLinearSplit

open Classical BoundarySector FixedCollisions FixedData CoefficientDecomposition FixedDataFunctions
open WeldedPath.WeightedCoefficients WeldedPath.HilbertSupport
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}

def fixedStatus (H : AbsForest n) (s a : Fin H.k) (b : Bool)
    (φ : Fin H.k → Label n) : Prop := (s ∈ H.Sfix φ a) ↔ b = true

theorem fixedStatus_factors (H : AbsForest n) (hH : H.IsValid)
    (s a : Fin H.k) (b : Bool) :
    Function.FactorsThrough (fixedStatus H s a b) (fun φ => H.Wfix φ a) := by
  intro φ ψ h
  unfold fixedStatus
  rw [sfix_eq_of_wfix_eq H hH a φ ψ h]

noncomputable def splitMap (H : AbsForest n) (B : Finset ℕ)
    (F : Finset (Fin H.k)) (s a : Fin H.k) (b : Bool) :
    Hil (Fin H.k → Label n) →ₗ[ℂ] Hil (Fin H.k → Label n) :=
  ((eventSpace (fixedStatus H s a b)).starProjection.toLinearMap).comp
    ((sectorSpace l G H B F).starProjection.toLinearMap)

theorem splitMap_apply (H : AbsForest n) (B : Finset ℕ)
    (F : Finset (Fin H.k)) (s a : Fin H.k) (b : Bool)
    (f : Hil (Fin H.k → Label n)) (φ : Fin H.k → Label n) :
    splitMap (l := l) (G := G) H B F s a b f φ =
      if fixedStatus H s a b φ then (sectorSpace l G H B F).starProjection f φ else 0 := by
  change ((eventSpace (fixedStatus H s a b)).starProjection _ ) φ = _
  rw [eventSpace_projection, diagProj_apply]
  rfl

theorem splitMap_mem (H : AbsForest n) (hH : H.IsValid) (B : Finset ℕ)
    (F : Finset (Fin H.k)) (s a : Fin H.k) (ha : a ∈ F) (b : Bool)
    (f : Hil (Fin H.k → Label n)) :
    splitMap (l := l) (G := G) H B F s a b f ∈
      dataSpace (anchoredWeight l G H B F a) (fun φ => H.Wfix φ a) := by
  apply dataSpace_mask_closed _ _ _ (fixedStatus_factors H hH s a b)
  rw [← sectorSpace_eq_dataSpace H B F a ha]
  exact (sectorSpace l G H B F).starProjection_apply_mem f

theorem splitMap_sum (H : AbsForest n) (B : Finset ℕ)
    (F : Finset (Fin H.k)) (s a : Fin H.k)
    (f : Hil (Fin H.k → Label n)) (hf : f ∈ sectorSpace l G H B F) :
    (∑ b : Bool, splitMap (l := l) (G := G) H B F s a b f) = f := by
  rw [Fintype.sum_bool]
  ext φ
  simp only [PiLp.add_apply, splitMap_apply,
    (sectorSpace l G H B F).starProjection_eq_self_iff.mpr hf]
  by_cases h : s ∈ H.Sfix φ a <;> simp [fixedStatus, h]

theorem splitMap_support (H : AbsForest n) (B : Finset ℕ)
    (F : Finset (Fin H.k)) (s a : Fin H.k) (b : Bool)
    (f : Hil (Fin H.k → Label n)) (φ : Fin H.k → Label n)
    (hf : splitMap (l := l) (G := G) H B F s a b f φ ≠ 0) :
    b = true ↔ s ∈ H.Sfix φ a := by
  have hp : fixedStatus H s a b φ := by
    by_contra hp
    exact hf (by rw [splitMap_apply, if_neg hp])
  exact hp.symm

theorem splitMap_weighted_orthogonal (H : AbsForest n) (B : Finset ℕ)
    (F : Finset (Fin H.k)) (s a : Fin H.k) (b c : Bool) (hbc : b ≠ c)
    (m : Data H → ℂ) (f g : Hil (Fin H.k → Label n)) :
    inner ℂ (rootMultiplier H s m (splitMap (l := l) (G := G) H B F s a b f))
      (rootMultiplier H s m (splitMap (l := l) (G := G) H B F s a c g)) = 0 := by
  simp only [PiLp.inner_apply]
  apply Finset.sum_eq_zero
  intro φ _
  cases b <;> cases c <;> try exact (hbc rfl).elim
  all_goals
    by_cases h : s ∈ H.Sfix φ a <;>
      simp [rootMultiplier, splitMap_apply, fixedStatus, h]

theorem self_mem_sfix (H : AbsForest n) (φ : Fin H.k → Label n) (s : Fin H.k) :
    s ∈ H.Sfix φ s := by
  apply ctree_subset_sfix H φ s
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, SimpleGraph.Reachable.refl _⟩

theorem adjacent_mem_sfix (H : AbsForest n) (hH : H.IsValid)
    (φ : Fin H.k → Label n) (s v : Fin H.k) (hsv : H.graph.Adj s v) :
    s ∈ H.Sfix φ v := by
  have hv : v ∈ H.Ctree φ v :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, SimpleGraph.Reachable.refl _⟩
  rcases hsv.2 with h | h
  · exact (edge_endpoints_mem_sfix H hH φ v (s, v) h (Or.inr hv)).1
  · exact (edge_endpoints_mem_sfix H hH φ v (v, s) h (Or.inl hv)).2

end WeldedPath.Supplement.AnchoredLinearSplit

end

-- Solutions.WeldedPathSectorLinearAssembly
section

namespace WeldedPath.SectorLinearAssembly

open Classical WeightedCoefficients HilbertSupport SectorStability
open scoped BigOperators

variable {Ω I J M : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype I] [Fintype J]

theorem partition_projection_sum (P : I → Ω → Prop) (hp : ∀ ω, ∃! i, P i ω)
    (f : Hil Ω) : (∑ i, (eventSpace (P i)).starProjection f) = f := by
  ext ω
  simp only [WithLp.ofLp_sum, Finset.sum_apply, eventSpace_projection, diagProj_apply]
  obtain ⟨i, hi, hu⟩ := hp ω
  rw [Finset.sum_eq_single i]
  · exact if_pos hi
  · intro j _ hji
    exact if_neg (fun hj => hji (hu j hj))
  · simp

theorem disjoint_support_inner (P : I → Ω → Prop) (hp : ∀ ω, ∃! i, P i ω)
    (i j : I) (hij : i ≠ j) (f g : Hil Ω)
    (hf : f ∈ eventSpace (P i)) (hg : g ∈ eventSpace (P j)) : inner ℂ f g = 0 := by
  simp only [PiLp.inner_apply]
  apply Finset.sum_eq_zero
  intro ω _
  by_cases hi : P i ω
  · have hj : ¬P j ω := fun hj => hij ((hp ω).unique hi hj)
    simp [hg ω hj]
  · simp [hf ω hi]

/-- Linear, weighted-orthogonal resolutions on disjoint coordinate sectors
assemble with no loss depending on the number of sectors. -/
theorem assemble (P : I → Ω → Prop) (hp : ∀ ω, ∃! i, P i ω)
    (S : I → Submodule ℂ (Hil Ω)) (hS : ∀ i, S i ≤ eventSpace (P i))
    (mul : M → Hil Ω →ₗ[ℂ] Hil Ω)
    (hmul : ∀ m f ω, f ω = 0 → mul m f ω = 0)
    (L : I → J → Hil Ω →ₗ[ℂ] Hil Ω)
    (hL : ∀ i j f, L i j f ∈ S i)
    (hsum : ∀ i f, f ∈ S i → (∑ j, L i j f) = f)
    (horth : ∀ i m j k, j ≠ k → ∀ f g,
      inner ℂ (mul m (L i j f)) (mul m (L i k g)) = 0) :
    ∃ D : I × J → Hil Ω →ₗ[ℂ] Hil Ω,
      (∀ i f, D i f = L i.1 i.2 ((eventSpace (P i.1)).starProjection f)) ∧
      (∀ i f, D i f ∈ S i.1) ∧
      (∀ f ∈ ⨆ i, S i, (∑ i, D i f) = f) ∧
      (∀ m i j, i ≠ j → ∀ f g, inner ℂ (mul m (D i f)) (mul m (D j g)) = 0) := by
  let D : I × J → Hil Ω →ₗ[ℂ] Hil Ω := fun i =>
    (L i.1 i.2).comp ((eventSpace (P i.1)).starProjection.toLinearMap)
  refine ⟨D, fun _ _ => rfl, fun i f => hL i.1 i.2 _, ?_, ?_⟩
  · intro f hf
    change (∑ i : I × J, L i.1 i.2 ((eventSpace (P i.1)).starProjection f)) = f
    rw [Fintype.sum_prod_type]
    calc
      _ = ∑ i, (eventSpace (P i)).starProjection f := by
        apply Finset.sum_congr rfl
        intro i _
        exact hsum i _ (sector_projection_mem P hp S hS i f hf)
      _ = f := partition_projection_sum P hp f
  · rintro m ⟨i, j⟩ ⟨k, t⟩ hne f g
    by_cases hik : i = k
    · subst k
      exact horth i m j t (fun h => hne (by cases h; rfl)) _ _
    · apply disjoint_support_inner P hp i k hik
      · intro ω hω
        exact hmul m _ ω (hS i (hL i j _) ω hω)
      · intro ω hω
        exact hmul m _ ω (hS k (hL k t _) ω hω)

end WeldedPath.SectorLinearAssembly

end

-- Solutions.WeldedPathAllSectorLinear
section

namespace WeldedPath.Supplement.AllSectorLinear

open Classical BoundarySector AllBoundaryStability AnchoredLinearSplit
open CoefficientDecomposition FixedDataFunctions EdgeCoefficientSplit
open WeldedPath.WeightedCoefficients WeldedPath.HilbertSupport WeldedPath.SectorLinearAssembly
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}

noncomputable def anchor (H : AbsForest n) (s : Fin H.k) (F : Finset (Fin H.k)) : Fin H.k :=
  if h : F.Nonempty then F.min' h else s

theorem anchor_mem (H : AbsForest n) (s : Fin H.k) (F : Finset (Fin H.k)) (hF : F ≠ ∅) :
    anchor H s F ∈ F := by
  have hn := Finset.nonempty_iff_ne_empty.mpr hF
  simp only [anchor, dif_pos hn]
  exact Finset.min'_mem F hn

abbrev Index (H : AbsForest n) := Finset (Fin H.k) × (Fin H.k × Bool)

noncomputable def vertex (H : AbsForest n) (s : Fin H.k) (i : Index H) : Fin H.k :=
  if i.1 = ∅ then i.2.1 else anchor H s i.1

noncomputable def weight (l : ℕ) (G : WeldedInstance n) (H : AbsForest n)
    (B : Finset ℕ) (s : Fin H.k) (i : Index H) : (Fin H.k → Label n) → ℝ :=
  if i.1 = ∅ then FiberCollision.avoidWeight l G H B
  else anchoredWeight l G H B i.1 (anchor H s i.1)

def fixed (H : AbsForest n) (s : Fin H.k) (i : Index H) : Prop :=
  if i.1 = ∅ then i.2.1 = s ∨ H.graph.Adj s i.2.1 else i.2.2 = true

theorem weight_nonneg (H : AbsForest n) (hH : H.IsValid) (B : Finset ℕ)
    (s : Fin H.k) (i : Index H) (φ : Fin H.k → Label n) :
    0 ≤ weight l G H B s i φ := by
  unfold weight
  split
  · exact FiberCollision.avoidWeight_nonneg H hH B φ
  · exact anchoredWeight_nonneg H hH B i.1 (anchor H s i.1) φ

theorem local_le_sector (H : AbsForest n) (B : Finset ℕ) (s : Fin H.k) (i : Index H) :
    dataSpace (weight l G H B s i) (fun φ => H.Wfix φ (vertex H s i)) ≤
      sectorSpace l G H B i.1 := by
  by_cases hF : i.1 = ∅
  · simp only [weight, vertex, hF, if_true]
    rw [sectorSpace_empty_eq]
    exact le_iSup (fun v => localCoefficientSpace H (FiberCollision.avoidWeight l G H B) v) i.2.1
  · simp only [weight, vertex, hF, if_false]
    rw [sectorSpace_eq_dataSpace H B i.1 (anchor H s i.1) (anchor_mem H s i.1 hF)]

/-- One fixed linear decomposition covers all exact boundary patterns.
Each summand has an index-fixed free/fixed status for the tested root. -/
theorem rooted_all_sector_linear (l : ℕ) (G : WeldedInstance n) (hG : G.IsValid)
    (H : AbsForest n) (hH : H.IsValid) (B : Finset ℕ) (s : Fin H.k)
    (hs : ∀ u, H.graph.Reachable s u) :
    ∃ D : Index H → Hil (Fin H.k → Label n) →ₗ[ℂ] Hil (Fin H.k → Label n),
      (∀ i f, D i f ∈ dataSpace (weight l G H B s i) (fun φ => H.Wfix φ (vertex H s i))) ∧
      (∀ f ∈ allSectorSpace l G H B, (∑ i, D i f) = f) ∧
      (∀ m : Data H → ℂ, ∀ i j, i ≠ j → ∀ f g,
        inner ℂ (rootMultiplier H s m (D i f)) (rootMultiplier H s m (D j g)) = 0) ∧
      (∀ i f φ, D i f φ ≠ 0 → (fixed H s i ↔ s ∈ H.Sfix φ (vertex H s i))) := by
  obtain ⟨E, hE, hsumE, horthE, hsupportE⟩ := rooted_linear_decomposition
    l G hG H hH s hs (fun _ x => x.val ∉ B)
  let L : Finset (Fin H.k) → (Fin H.k × Bool) →
      Hil (Fin H.k → Label n) →ₗ[ℂ] Hil (Fin H.k → Label n) := fun F vb =>
    if F = ∅ then (if vb.2 = true then 0 else E vb.1)
    else if vb.1 = anchor H s F then splitMap (l := l) (G := G) H B F s (anchor H s F) vb.2 else 0
  have hlocal : ∀ F vb f, L F vb f ∈
      dataSpace (weight l G H B s (F, vb)) (fun φ => H.Wfix φ (vertex H s (F, vb))) := by
    intro F vb f
    by_cases hF : F = ∅
    · simp only [L, weight, vertex, hF, if_true]
      by_cases hb : vb.2 = true
      · simp [hb]
      · simpa only [hb, Bool.false_eq_true, if_false, localCoefficientSpace,
          FiberCollision.avoidWeight] using hE vb.1 f
    · simp only [L, weight, vertex, hF, if_false]
      by_cases hv : vb.1 = anchor H s F
      · rw [if_pos hv]
        exact splitMap_mem H hH B F s (anchor H s F) (anchor_mem H s F hF) vb.2 f
      · simp [hv]
  have hL : ∀ F vb f, L F vb f ∈ sectorSpace l G H B F :=
    fun F vb f => local_le_sector H B s (F, vb) (hlocal F vb f)
  have hsum : ∀ F f, f ∈ sectorSpace l G H B F → (∑ vb, L F vb f) = f := by
    intro F f hf
    by_cases hF : F = ∅
    · subst F
      simp only [L, if_true, Fintype.sum_prod_type, Fintype.sum_bool,
        Bool.false_eq_true, if_false, LinearMap.zero_apply, zero_add]
      apply hsumE
      simpa only [sectorSpace_empty_eq, FiberCollision.avoidWeight] using hf
    · have he (v : Fin H.k) : (∑ b : Bool, L F (v, b) f) =
          if v = anchor H s F then f else 0 := by
        by_cases hv : v = anchor H s F
        · simp only [L, hF, if_false, hv, if_true]
          exact splitMap_sum H B F s (anchor H s F) f hf
        · simp [L, hF, hv]
      rw [Fintype.sum_prod_type]
      simp_rw [he]
      simp
  have horth : ∀ F m vb wb, vb ≠ wb → ∀ f g,
      inner ℂ (rootMultiplier H s m (L F vb f)) (rootMultiplier H s m (L F wb g)) = 0 := by
    intro F m ⟨v, b⟩ ⟨w, c⟩ hne f g
    by_cases hF : F = ∅
    · simp only [L, hF, if_true]
      cases b <;> cases c <;> simp only [Bool.false_eq_true, if_false, if_true,
        LinearMap.zero_apply, map_zero, inner_zero_left, inner_zero_right]
      exact horthE m v w (fun h => hne (by cases h; rfl)) f g
    · simp only [L, hF, if_false]
      by_cases hv : v = anchor H s F
      · by_cases hw : w = anchor H s F
        · rw [if_pos hv, if_pos hw]
          exact splitMap_weighted_orthogonal H B F s (anchor H s F) b c
            (fun he => hne (Prod.ext (hv.trans hw.symm) he)) m f g
        · simp [hw]
      · simp [hv]
  obtain ⟨D, hD, _, hsumD, horthD⟩ := assemble
    (boundaryPattern H B) (boundary_pattern_partition H B) (sectorSpace l G H B)
    (sectorSpace_le_event H B) (rootMultiplier H s)
    (fun m f φ hf => by change m (H.Wfix φ s) * f φ = 0; rw [hf, mul_zero])
    L hL hsum horth
  refine ⟨D, ?_, hsumD, horthD, ?_⟩
  · intro i f
    rw [hD]
    exact hlocal i.1 i.2 _
  · rintro ⟨F, v, b⟩ f φ hne
    rw [hD] at hne
    by_cases hF : F = ∅
    · simp only [fixed, vertex, hF, if_true]
      have hb : b ≠ true := by
        intro hb
        simp [L, hF, hb] at hne
      have hEne : E v ((eventSpace (boundaryPattern H B F)).starProjection f) φ ≠ 0 := by
        simpa only [L, hF, if_true, hb, Bool.false_eq_true, if_false] using hne
      constructor
      · rintro (rfl | hadj)
        · exact self_mem_sfix H φ _
        · exact adjacent_mem_sfix H hH φ s v hadj
      · intro hfix
        rcases hsupportE v _ φ hEne with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exact (h hfix).elim
    · have hv : v = anchor H s F := by
        by_contra hv
        simp [L, hF, hv] at hne
      simp only [fixed, vertex, hF, if_false]
      apply splitMap_support H B F s (anchor H s F) b _ φ
      simpa only [L, hF, if_false, hv, if_true] using hne

end WeldedPath.Supplement.AllSectorLinear

end

-- Solutions.WeldedPathRootData
section

namespace WeldedPath.Supplement.CoefficientDecomposition

open Classical FixedData FixedDataFunctions
open WeldedPath.WeightedCoefficients WeldedPath.HilbertSupport

variable {n : ℕ}

noncomputable def fixedRootValue (H : AbsForest n) (a v : Fin H.k) (d : Data H) : Label n :=
  if h : ∃ φ : Fin H.k → Label n, H.Wfix φ v = d ∧ a ∈ H.Sfix φ v then
    (Classical.choose h) a else 0

theorem fixedRootValue_eq (H : AbsForest n) (hH : H.IsValid) (a v : Fin H.k)
    (φ : Fin H.k → Label n) (ha : a ∈ H.Sfix φ v) :
    fixedRootValue H a v (H.Wfix φ v) = φ a := by
  have hex : ∃ ψ : Fin H.k → Label n,
      H.Wfix ψ v = H.Wfix φ v ∧ a ∈ H.Sfix ψ v := ⟨φ, rfl, ha⟩
  rw [fixedRootValue, dif_pos hex]
  exact (wfix_eq_iff_agree_sfix H hH (Classical.choose hex) φ v).mp
    (Classical.choose_spec hex).1 a ha

theorem root_mem_sfix (H : AbsForest n) (φ : Fin H.k → Label n) (s : Fin H.k) :
    s ∈ H.Sfix φ s :=
  ctree_subset_sfix H φ s (Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, SimpleGraph.Reachable.refl _⟩)

theorem root_label_projection (H : AbsForest n) (hH : H.IsValid) (s : Fin H.k)
    (z : Label n) (f : Hil (Fin H.k → Label n)) :
    (eventSpace (fun φ : Fin H.k → Label n => φ s = z)).starProjection f =
      rootMultiplier H s (fun d => if fixedRootValue H s s d = z then 1 else 0) f := by
  ext φ
  rw [eventSpace_projection, diagProj_apply]
  change (if φ s = z then f φ else 0) =
    (if fixedRootValue H s s (H.Wfix φ s) = z then 1 else 0) * f φ
  rw [fixedRootValue_eq H hH s s φ (root_mem_sfix H φ s)]
  split_ifs <;> simp

end WeldedPath.Supplement.CoefficientDecomposition

end

-- Solutions.WeldedPathConnectedResolution
section

namespace WeldedPath.Supplement.ConnectedResolution

open Classical AllSectorLinear AllBoundaryStability BoundarySector CoefficientDecomposition
open FixedDataFunctions ConnectedConcentration EdgeCoefficientSplit
open WeldedPath.WeightedCoefficients WeldedPath.ProductDecomposition

variable {n l : ℕ} {G : WeldedInstance n}

theorem avoid_weight_witness (H : AbsForest n) (hH : H.IsValid) (B : Finset ℕ)
    (v : Fin H.k) (hv : ∀ u, H.graph.Reachable v u) (φ₀ : Fin H.k → Label n)
    (hpos : 0 < FiberCollision.avoidWeight l G H B φ₀) :
    H.muRef l G φ₀ ≠ 0 ∧ ∀ φ,
      (if H.Wfix φ v = H.Wfix φ₀ v then FiberCollision.avoidWeight l G H B φ else 0) =
        sourceWeight l G H φ₀ v B φ := by
  have ha : ∀ u, (φ₀ u).val ∉ B := by
    by_contra ha
    have hz : FiberCollision.avoidWeight l G H B φ₀ = 0 := by
      simp only [FiberCollision.avoidWeight, maskedReference, if_neg ha]
    rw [hz] at hpos
    exact (lt_irrefl 0) hpos
  have href : 0 < H.muRef l G φ₀ := by
    simpa only [FiberCollision.avoidWeight, maskedReference, if_pos ha] using hpos
  exact ⟨ne_of_gt href, FiberCollision.fiber_weight_eq_source H hH v hv B φ₀ ha⟩

theorem weight_source (H : AbsForest n) (hH : H.IsValid) (B : Finset ℕ)
    (s : Fin H.k) (hs : ∀ u, H.graph.Reachable s u) (i : Index H)
    (φ₀ : Fin H.k → Label n) (hpos : 0 < weight l G H B s i φ₀) :
    H.muRef l G φ₀ ≠ 0 ∧ ∀ φ,
      (if H.Wfix φ (vertex H s i) = H.Wfix φ₀ (vertex H s i) then
        weight l G H B s i φ else 0) = sourceWeight l G H φ₀ (vertex H s i) B φ := by
  by_cases hF : i.1 = ∅
  · have hv : ∀ u, H.graph.Reachable i.2.1 u := fun u => (hs i.2.1).symm.trans (hs u)
    simpa only [weight, vertex, hF, if_true] using
      avoid_weight_witness H hH B i.2.1 hv φ₀ (by simpa only [weight, hF, if_true] using hpos)
  · have hv : ∀ u, H.graph.Reachable (anchor H s i.1) u :=
      fun u => (hs (anchor H s i.1)).symm.trans (hs u)
    simpa only [weight, vertex, hF, if_false] using
      anchored_weight_witness H hH B i.1 (anchor H s i.1) hv φ₀
        (by simpa only [weight, hF, if_false] using hpos)

/-- All fields of the abstract component-resolution interface are realized
by the canonical welded-tree weights and fixed-data maps. In particular, the
conditional one-point cap is a proved property of these weights. -/
theorem connectedResolution (H : AbsForest n) (hH : H.IsValid)
    (s : Fin H.k) (hs : ∀ u, H.graph.Reachable s u)
    (hG : G.IsValid) (hn : 16 ≤ n) (hl : 2 ≤ l) (hln : l ≤ n - 4)
    (B : Finset ℕ) (hB : Vbd n l ⊆ B) (hBw : Disjoint B (Vweld n))
    (hsmall : (H.k : ℝ) * (B.card : ℝ) * (4 / (2 : ℝ) ^ n) ≤ 1 / 2) :
    ∃ R : ComponentResolution (Fin H.k → Label n) (Index H) (Data H) (Label n)
      (8 / (2 : ℝ) ^ n),
      R.space = allSectorSpace l G H B ∧ R.root = (fun φ => φ s) := by
  obtain ⟨D, hD, hsum, horth, hsupport⟩ := rooted_all_sector_linear l G hG H hH B s hs
  refine ⟨{
    space := allSectorSpace l G H B
    root := fun φ => φ s
    op := D
    weight := weight l G H B s
    data := fun i φ => H.Wfix φ (vertex H s i)
    fixed := fixed H s
    free := fun i φ => s ∉ H.Sfix φ (vertex H s i)
    decode := fun i => fixedRootValue H s (vertex H s i)
    weight_nonneg := weight_nonneg H hH B s
    local_le := ?_
    range_mem := hD
    sum_apply := hsum
    orthogonal := ?_
    fiber_orthogonal := ?_
    free_support := ?_
    fixed_value := ?_
    point_cap := ?_
  }, rfl, rfl⟩
  · intro i
    exact (local_le_sector H B s i).trans (le_iSup (sectorSpace l G H B) i.1)
  · intro i j hij f g
    simpa only [rootMultiplier_one] using horth (fun _ => 1) i j hij f g
  · intro i j hij z f g
    rw [root_label_projection H hH s z, root_label_projection H hH s z]
    exact horth _ i j hij f g
  · intro i hfree f φ hn
    by_contra hne
    exact hfree ((hsupport i f φ hne).mpr (not_not.mp hn))
  · intro i hi f φ hne
    exact (fixedRootValue_eq H hH s (vertex H s i) φ ((hsupport i f φ hne).mp hi)).symm
  · intro i d z
    have hv : ∀ u, H.graph.Reachable (vertex H s i) u :=
      fun u => (hs (vertex H s i)).symm.trans (hs u)
    have hc := SourceFiberBound.free_point_fiber_bound H hH (weight l G H B s i)
      (weight_nonneg H hH B s i) (vertex H s i) hv hG hn hl hln B hB hBw hsmall
      (weight_source H hH B s hs i) s z d
    convert hc using 1 <;> congr 1
    funext φ
    split_ifs <;> rfl

end WeldedPath.Supplement.ConnectedResolution

end

-- Solutions.WeldedPathConnectedInternalCollision
section

namespace WeldedPath.Supplement.ConnectedResolution

open Classical AllSectorLinear AllBoundaryStability BoundarySector FixedCollisions
open FixedDataFunctions
open WeldedPath.WeightedCoefficients WeldedPath.ProductDecomposition
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n} {Y : Type*} [Fintype Y] [DecidableEq Y]

/-- Actual within-component collision bound, retaining all other connected
components in a constrained spectator coefficient space. -/
theorem internal_collision_with_spectator (H : AbsForest n) (hH : H.IsValid)
    (a b : Fin H.k) (ha : ∀ u, H.graph.Reachable a u)
    (hG : G.IsValid) (hn : 16 ≤ n) (hl : 2 ≤ l) (hln : l ≤ n - 4)
    (B : Finset ℕ) (hB : Vbd n l ⊆ B) (hBw : Disjoint B (Vweld n))
    (hsmall : (H.k : ℝ) * (B.card : ℝ) * (4 / (2 : ℝ) ^ n) ≤ 1 / 2)
    (T : Submodule ℂ (Hil Y))
    (Good : Submodule ℂ (Hil ((Fin H.k → Label n) × Y)))
    (hbad : eventSpace (fun p : (Fin H.k → Label n) × Y => Collision H a b p.1) ≤ Goodᗮ)
    (f : Hil ((Fin H.k → Label n) × Y))
    (hf : f ∈ tensorSpace (allSectorSpace l G H B) T)
    (hminimal : f ∈ (tensorSpace (allSectorSpace l G H B) T ⊓ Goodᗮ)ᗮ) :
    ‖(eventSpace (fun p : (Fin H.k → Label n) × Y => Collision H a b p.1)).starProjection f‖ ^ 2 ≤
      ((H.k : ℝ) * 2) * (96 * ((n : ℝ) + 1) / (2 : ℝ) ^ n) * ‖f‖ ^ 2 := by
  obtain ⟨D, hD, hsum, horth, _hsupport⟩ :=
    rooted_all_sector_linear l G hG H hH B a ha
  have hfactor (i : Index H) : ∃ Q : Data H → Prop,
      ∀ φ, FixedCollision H (vertex H a i) a b φ ↔ Q (H.Wfix φ (vertex H a i)) := by
    obtain ⟨Q,hQ⟩ := (Function.factorsThrough_iff (FixedCollision H (vertex H a i) a b)).mp
      (fixedCollision_factors H hH (vertex H a i) a b)
    exact ⟨Q, fun φ => Iff.of_eq (congrFun hQ φ)⟩
  choose Q hQ using hfactor
  have hbnd := resolved_internal_collision_with_spectator
    (allSectorSpace l G H B) T D (weight l G H B a)
    (fun i φ => H.Wfix φ (vertex H a i)) (weight_nonneg H hH B a)
    (fun i => (local_le_sector H B a i).trans (le_iSup (sectorSpace l G H B) i.1))
    hD hsum
    (by
      intro i j hij g h
      simpa only [CoefficientDecomposition.rootMultiplier_one] using
        horth (fun _ => 1) i j hij g h)
    (boundaryPattern H B)
    (by
      intro F E hne φ hF hE
      apply hne
      ext u
      exact (hF u).symm.trans (hE u))
    (by
      intro i g φ hp
      exact (sectorSpace_le_event H B i.1 ((local_le_sector H B a i) (hD i g))) φ hp)
    (Collision H a b) (fun i => FixedCollision H (vertex H a i) a b) Q
    hQ (fun _ _ hf => hf.1)
    (96 * ((n : ℝ) + 1) / (2 : ℝ) ^ n) (by positivity)
    (by
      intro i d
      have hv : ∀ u, H.graph.Reachable (vertex H a i) u :=
        fun u => (ha (vertex H a i)).symm.trans (ha u)
      have hc := SourceFiberBound.free_collision_fiber_bound H hH (weight l G H B a i)
        (weight_nonneg H hH B a i) (vertex H a i) hv hG hn hl hln B hB hBw hsmall
        (weight_source H hH B a ha i) a b d
      convert hc using 1
      apply Finset.sum_congr rfl
      intro φ _
      have he : (H.Wfix φ (vertex H a i) = d ∧
          (Collision H a b φ ∧ ¬FixedCollision H (vertex H a i) a b φ)) ↔
          H.Wfix φ (vertex H a i) = d ∧ FreeCollision H (vertex H a i) a b φ := by
        unfold FixedCollision FreeCollision
        tauto
      exact if_congr he rfl rfl)
    Good hbad f hf hminimal
  simpa only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, Nat.cast_mul,
    Nat.cast_ofNat] using hbnd

end WeldedPath.Supplement.ConnectedResolution

end

-- Solutions.WeldedPathResolvedCrossSpectator
section

namespace WeldedPath.ProductDecomposition

open Classical HilbertSupport WeightedCoefficients CoefficientStability
open scoped BigOperators

variable {X Y W A B Z ι κ : Type*} [Fintype X] [Fintype Y] [Fintype W]
  [Fintype ι] [Fintype κ] [DecidableEq X] [DecidableEq Y] [DecidableEq W]
  [DecidableEq A] [DecidableEq B]

/-- The cross-component one-point estimate with all remaining components
retained as an arbitrary constrained spectator coefficient space. -/
theorem resolved_cross_collision_with_spectator (ε : ℝ) (hε : 0 ≤ ε)
    (L : ComponentResolution X ι A Z ε) (R : ComponentResolution Y κ B Z ε)
    (T : Submodule ℂ (Hil W)) (Good : Submodule ℂ (Hil ((X × Y) × W)))
    (hbad : eventSpace (fun p : (X × Y) × W => L.root p.1.1 = R.root p.1.2) ≤ Goodᗮ)
    (f : Hil ((X × Y) × W)) (hf : f ∈ tensorSpace (tensorSpace L.space R.space) T)
    (hminimal : f ∈ (tensorSpace (tensorSpace L.space R.space) T ⊓ Goodᗮ)ᗮ) :
    ‖(eventSpace (fun p : (X × Y) × W => L.root p.1.1 = R.root p.1.2)).starProjection f‖ ^ 2 ≤
      ε * ‖f‖ ^ 2 := by
  let D : ι × κ → Hil (X × Y) →ₗ[ℂ] Hil (X × Y) :=
    fun ij => linearTensor (L.op ij.1) (R.op ij.2)
  have hlocal (ij : ι × κ) (g : Hil (X × Y)) : D ij g ∈ dataSpace
      (fun p : X × Y => L.weight ij.1 p.1 * R.weight ij.2 p.2)
      (fun p => (L.data ij.1 p.1, R.data ij.2 p.2)) :=
    linearTensor_mem_dataSpace _ _ (L.weight_nonneg ij.1) _ _ _ _
      (L.range_mem ij.1) (R.range_mem ij.2) g
  apply spectator_collision_bound (tensorSpace L.space R.space) T
    (fun p : X × Y => L.root p.1 = R.root p.2) D (fun ij => L.fixed ij.1 ∧ R.fixed ij.2)
    ?_ ?_ ?_ ?_ ε hε ?_ Good hbad f hf hminimal
  · intro g hg
    exact product_resolution L.space R.space L.op R.op L.sum_apply R.sum_apply g
      ((mem_tensorSpace _ _ g).mp hg).1 ((mem_tensorSpace _ _ g).mp hg).2
  · intro i j hij g h
    exact product_orthogonal L.op R.op L.orthogonal R.orthogonal i j hij g h
  · intro i j hij g h
    exact product_collision_orthogonal L.root R.root L.op R.op
      (fun i j hij y g h => L.fiber_orthogonal i j hij (R.root y) g h)
      (fun i j hij x g h => by
        have hh := R.fiber_orthogonal i j hij (L.root x) g h
        simpa only [eq_comm] using hh) i j hij g h
  · intro ij hij g _hg
    have hmasked : (eventSpace (fun p : X × Y => L.root p.1 = R.root p.2)).starProjection
        (D ij g) ∈ dataSpace
          (fun p : X × Y => L.weight ij.1 p.1 * R.weight ij.2 p.2)
          (fun p => (L.data ij.1 p.1, R.data ij.2 p.2)) := by
      apply masked_mem_dataSpace_of_support _ _ _
        (fun d : A × B => L.decode ij.1 d.1 = R.decode ij.2 d.2) _ (hlocal ij g)
      rintro ⟨x,y⟩ hxy
      have hx : L.root x = L.decode ij.1 (L.data ij.1 x) := by
        apply L.fixed_value ij.1 hij.1 (column (rightAction (R.op ij.2) g) y) x
        simpa only [D, linearTensor_column] using hxy
      have hy : R.root y = R.decode ij.2 (R.data ij.2 y) := by
        by_contra hn
        have hz : D ij g (x,y) = 0 := linearTensor_support_right _ _
          (fun y => R.root y = R.decode ij.2 (R.data ij.2 y))
          (fun h y hne => by
            by_contra hng
            exact hne (R.fixed_value ij.2 hij.2 h y hng)) g x y hn
        exact hxy hz
      simp only [hx, hy]
    exact local_product_le_tensorSpace _ _ (L.weight_nonneg ij.1) _ _ L.space R.space
      (L.local_le ij.1) (R.local_le ij.2) hmasked
  · intro ij hij g
    by_cases hL : L.fixed ij.1
    · have hR : ¬R.fixed ij.2 := fun hR => hij ⟨hL,hR⟩
      exact product_point_energy_bound_right _ _ (L.weight_nonneg ij.1) (R.weight_nonneg ij.2)
        _ _ L.root R.root (R.free ij.2) ε (R.point_cap ij.2) _ (hlocal ij g)
        (fun x y hy => linearTensor_support_right _ _ _ (R.free_support ij.2 hR) g x y hy)
    · exact product_point_energy_bound _ _ (L.weight_nonneg ij.1) (R.weight_nonneg ij.2)
        _ _ L.root R.root (L.free ij.1) ε (L.point_cap ij.1) _ (hlocal ij g)
        (fun x y hx => linearTensor_support_left _ _ _ (L.free_support ij.1 hL) g x y hx)

end WeldedPath.ProductDecomposition

end

-- Solutions.WeldedPathConnectedCrossCollision
section

namespace WeldedPath.Supplement.ConnectedResolution

open Classical AllBoundaryStability
open WeldedPath.WeightedCoefficients WeldedPath.ProductDecomposition

variable {n l : ℕ} {G : WeldedInstance n} {W : Type*} [Fintype W] [DecidableEq W]

/-- Actual cross-component collision bound, with arbitrary coefficient
entanglement and all remaining components retained as constrained spectators. -/
theorem cross_collision_with_spectator (H J : AbsForest n) (hH : H.IsValid) (hJ : J.IsValid)
    (a : Fin H.k) (b : Fin J.k)
    (ha : ∀ u, H.graph.Reachable a u) (hb : ∀ v, J.graph.Reachable b v)
    (hG : G.IsValid) (hn : 16 ≤ n) (hl : 2 ≤ l) (hln : l ≤ n - 4)
    (B : Finset ℕ) (hB : Vbd n l ⊆ B) (hBw : Disjoint B (Vweld n))
    (hHsmall : (H.k : ℝ) * (B.card : ℝ) * (4 / (2 : ℝ) ^ n) ≤ 1 / 2)
    (hJsmall : (J.k : ℝ) * (B.card : ℝ) * (4 / (2 : ℝ) ^ n) ≤ 1 / 2)
    (T : Submodule ℂ (Hil W))
    (Good : Submodule ℂ (Hil (((Fin H.k → Label n) × (Fin J.k → Label n)) × W)))
    (hbad : eventSpace (fun p : ((Fin H.k → Label n) × (Fin J.k → Label n)) × W =>
      p.1.1 a = p.1.2 b) ≤ Goodᗮ)
    (f : Hil (((Fin H.k → Label n) × (Fin J.k → Label n)) × W))
    (hf : f ∈ tensorSpace (tensorSpace (allSectorSpace l G H B) (allSectorSpace l G J B)) T)
    (hminimal : f ∈ (tensorSpace (tensorSpace (allSectorSpace l G H B) (allSectorSpace l G J B)) T ⊓ Goodᗮ)ᗮ) :
    ‖(eventSpace (fun p : ((Fin H.k → Label n) × (Fin J.k → Label n)) × W =>
      p.1.1 a = p.1.2 b)).starProjection f‖ ^ 2 ≤ (8 / (2 : ℝ) ^ n) * ‖f‖ ^ 2 := by
  obtain ⟨L, hLs, hLr⟩ := connectedResolution H hH a ha hG hn hl hln B hB hBw hHsmall
  obtain ⟨R, hRs, hRr⟩ := connectedResolution J hJ b hb hG hn hl hln B hB hBw hJsmall
  have hbad' : eventSpace (fun p : ((Fin H.k → Label n) × (Fin J.k → Label n)) × W =>
      L.root p.1.1 = R.root p.1.2) ≤ Goodᗮ := by
    simpa only [hLr, hRr] using hbad
  have hf' : f ∈ tensorSpace (tensorSpace L.space R.space) T := by
    simpa only [hLs, hRs] using hf
  have hm' : f ∈ (tensorSpace (tensorSpace L.space R.space) T ⊓ Goodᗮ)ᗮ := by
    simpa only [hLs, hRs] using hminimal
  have hh := resolved_cross_collision_with_spectator (8 / (2 : ℝ) ^ n) (by positivity)
    L R T Good hbad' f hf' hm'
  simpa only [hLr, hRr] using hh

end WeldedPath.Supplement.ConnectedResolution

end

-- Solutions.WeldedPathCoefficientTransport
section

namespace WeldedPath.CoefficientTransport

open Classical WeightedCoefficients HilbertSupport

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

noncomputable def reindex (e : X ≃ Y) : Hil X ≃ₗᵢ[ℂ] Hil Y :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e

@[simp] theorem reindex_apply (e : X ≃ Y) (f : Hil X) (y : Y) :
    reindex e f y = f (e.symm y) := rfl

theorem reindex_event (e : X ≃ Y) (P : X → Prop) (f : Hil X) :
    reindex e ((eventSpace P).starProjection f) =
      (eventSpace (fun y => P (e.symm y))).starProjection (reindex e f) := by
  ext y
  simp [eventSpace_projection, diagProj_apply]

theorem reindex_event_norm (e : X ≃ Y) (P : X → Prop) (f : Hil X) :
    ‖(eventSpace P).starProjection f‖ =
      ‖(eventSpace (fun y => P (e.symm y))).starProjection (reindex e f)‖ := by
  rw [← reindex_event, (reindex e).norm_map]

theorem map_eventSpace (e : X ≃ Y) (P : X → Prop) :
    (eventSpace P).map (reindex e).toLinearMap = eventSpace (fun y => P (e.symm y)) := by
  ext g
  constructor
  · rintro ⟨f,hf,rfl⟩ y hy
    exact hf (e.symm y) hy
  · intro hg
    refine ⟨(reindex e).symm g, ?_, (reindex e).apply_symm_apply g⟩
    intro x hx
    have he : (reindex e).symm g x = g (e x) := by
      have hh := congrArg (fun f : Hil Y => f (e x)) ((reindex e).apply_symm_apply g)
      simpa only [reindex_apply, Equiv.symm_apply_apply] using hh
    rw [he]
    exact hg (e x) (by simpa only [Equiv.symm_apply_apply] using hx)

theorem map_minimal {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (U : E ≃ₗᵢ[ℂ] F) (S R : Submodule ℂ E) (f : E)
    (hf : f ∈ (S ⊓ Rᗮ)ᗮ) :
    U f ∈ (S.map U.toLinearMap ⊓ (R.map U.toLinearMap)ᗮ)ᗮ := by
  have hmem : U f ∈ ((S ⊓ Rᗮ)ᗮ).map U.toLinearMap := ⟨f,hf,rfl⟩
  rw [(S ⊓ Rᗮ).map_orthogonal_equiv U,
    Submodule.map_inf U.toLinearMap U.injective, R.map_orthogonal_equiv U] at hmem
  exact hmem

end WeldedPath.CoefficientTransport

end

-- Solutions.WeldedPathDisconnectedPairs
section

namespace WeldedPath.Supplement.DisconnectedStability

open Classical ComponentForest AllBoundaryStability FixedCollisions
open WeldedPath.WeightedCoefficients WeldedPath.ProductDecomposition WeldedPath.CoefficientTransport
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}

noncomputable def componentSpaces (l : ℕ) (G : WeldedInstance n) (H : AbsForest n) (B : Finset ℕ)
    (s : Roots H) : Submodule ℂ (Hil (LocalAssignment H s)) :=
  allSectorSpace l G (componentForest H s.val) B

noncomputable abbrev coefficientSpace (l : ℕ) (G : WeldedInstance n) (H : AbsForest n)
    (B : Finset ℕ) : Submodule ℂ (Hil (Fin H.k → Label n)) :=
  productSpace H (componentSpaces l G H B)

theorem component_survival_budget (H : AbsForest n) (B : Finset ℕ)
    (hsmall : (H.k : ℝ) * (B.card : ℝ) * (4 / (2 : ℝ) ^ n) ≤ 1 / 2)
    (s : Roots H) :
    ((componentForest H s.val).k : ℝ) * (B.card : ℝ) * (4 / (2 : ℝ) ^ n) ≤ 1 / 2 := by
  apply le_trans _ hsmall
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact_mod_cast component_k_le H s.val

theorem internal_pair_bound (H : AbsForest n) (hH : H.IsValid)
    (hG : G.IsValid) (hn : 16 ≤ n) (hl : 2 ≤ l) (hln : l ≤ n - 4)
    (B : Finset ℕ) (hB : Vbd n l ⊆ B) (hBw : Disjoint B (Vweld n))
    (hsmall : (H.k : ℝ) * (B.card : ℝ) * (4 / (2 : ℝ) ^ n) ≤ 1 / 2)
    (r : Roots H) (i j : Fin (H.comp r.val).card)
    (f : Hil (Fin H.k → Label n)) (hf : f ∈ coefficientSpace l G H B)
    (hm : f ∈ (coefficientSpace l G H B ⊓ (eventSpace Function.Injective)ᗮ)ᗮ) :
    ‖(eventSpace (Collision H (vertexMap H r.val i) (vertexMap H r.val j))).starProjection f‖ ^ 2 ≤
      2 * (H.k : ℝ) * (96 * ((n : ℝ) + 1) / (2 : ℝ) ^ n) * ‖f‖ ^ 2 := by
  let S := componentSpaces l G H B
  let U := regroupOneHil H r
  let Good := eventSpace (fun p : LocalAssignment H r × OneSpectator H r =>
    Function.Injective ((regroupOne H r).symm p))
  have hGood : (eventSpace (Function.Injective : (Fin H.k → Label n) → Prop)).map U.toLinearMap = Good :=
    map_eventSpace (regroupOne H r) Function.Injective
  have hf' : U f ∈ tensorSpace (S r) (oneSpectatorSpace H S r) :=
    (regroupOne_mem_iff H S r f).mpr hf
  have hm' : U f ∈ (tensorSpace (S r) (oneSpectatorSpace H S r) ⊓ Goodᗮ)ᗮ := by
    have hh := map_minimal U (coefficientSpace l G H B) (eventSpace Function.Injective) f hm
    rw [regroupOne_productSpace H S r, hGood] at hh
    exact hh
  have hbad : eventSpace (fun p : LocalAssignment H r × OneSpectator H r =>
      Collision (componentForest H r.val) i j p.1) ≤ Goodᗮ := by
    dsimp only [Good]
    rw [eventSpace_orthogonal]
    apply WeldedPath.CollisionStability.eventSpace_mono
    intro p hp hinj
    apply hp.1
    apply vertexMap_injective H r.val
    apply hinj
    simpa only [regroupOne_label] using hp.2
  have hb := ConnectedResolution.internal_collision_with_spectator
    (componentForest H r.val) (component_valid H hH r.val) i j
    (component_connected H r.val i) hG hn hl hln B hB hBw
    (component_survival_budget H B hsmall r) (oneSpectatorSpace H S r) Good hbad (U f) hf' hm'
  have hevent : (fun p : LocalAssignment H r × OneSpectator H r =>
      Collision H (vertexMap H r.val i) (vertexMap H r.val j) ((regroupOne H r).symm p)) =
      (fun p => Collision (componentForest H r.val) i j p.1) := by
    funext p
    apply propext
    simp only [Collision, ne_eq, (vertexMap_injective H r.val).eq_iff, regroupOne_label]
  have he := reindex_event_norm (regroupOne H r)
    (Collision H (vertexMap H r.val i) (vertexMap H r.val j)) f
  rw [hevent] at he
  rw [he]
  change ‖(eventSpace (fun p : LocalAssignment H r × OneSpectator H r =>
    Collision (componentForest H r.val) i j p.1)).starProjection (U f)‖ ^ 2 ≤ _
  apply hb.trans
  rw [U.norm_map]
  have hk : ((componentForest H r.val).k : ℝ) ≤ (H.k : ℝ) := by
    exact_mod_cast component_k_le H r.val
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  nlinarith

theorem cross_pair_bound (H : AbsForest n) (hH : H.IsValid)
    (hG : G.IsValid) (hn : 16 ≤ n) (hl : 2 ≤ l) (hln : l ≤ n - 4)
    (B : Finset ℕ) (hB : Vbd n l ⊆ B) (hBw : Disjoint B (Vweld n))
    (hsmall : (H.k : ℝ) * (B.card : ℝ) * (4 / (2 : ℝ) ^ n) ≤ 1 / 2)
    (r s : Roots H) (hrs : r ≠ s)
    (i : Fin (H.comp r.val).card) (j : Fin (H.comp s.val).card)
    (f : Hil (Fin H.k → Label n)) (hf : f ∈ coefficientSpace l G H B)
    (hm : f ∈ (coefficientSpace l G H B ⊓ (eventSpace Function.Injective)ᗮ)ᗮ) :
    ‖(eventSpace (Collision H (vertexMap H r.val i) (vertexMap H s.val j))).starProjection f‖ ^ 2 ≤
      (8 / (2 : ℝ) ^ n) * ‖f‖ ^ 2 := by
  let S := componentSpaces l G H B
  let U := regroupTwoHil H r s hrs
  let Good := eventSpace (fun p : (LocalAssignment H r × LocalAssignment H s) × TwoSpectator H r s =>
    Function.Injective ((regroupTwo H r s hrs).symm p))
  have hGood : (eventSpace (Function.Injective : (Fin H.k → Label n) → Prop)).map U.toLinearMap = Good :=
    map_eventSpace (regroupTwo H r s hrs) Function.Injective
  have hf' : U f ∈ tensorSpace (tensorSpace (S r) (S s)) (twoSpectatorSpace H S r s) :=
    (regroupTwo_mem_iff H S r s hrs f).mpr hf
  have hm' : U f ∈ (tensorSpace (tensorSpace (S r) (S s)) (twoSpectatorSpace H S r s) ⊓ Goodᗮ)ᗮ := by
    have hh := map_minimal U (coefficientSpace l G H B) (eventSpace Function.Injective) f hm
    rw [regroupTwo_productSpace H S r s hrs, hGood] at hh
    exact hh
  have hne : vertexMap H r.val i ≠ vertexMap H s.val j := by
    intro h
    have he := (vertexSigma_bijective H).1 (a₁ := ⟨r,i⟩) (a₂ := ⟨s,j⟩) h
    exact hrs (congrArg Sigma.fst he)
  have hbad : eventSpace (fun p : (LocalAssignment H r × LocalAssignment H s) × TwoSpectator H r s =>
      p.1.1 i = p.1.2 j) ≤ Goodᗮ := by
    dsimp only [Good]
    rw [eventSpace_orthogonal]
    apply WeldedPath.CollisionStability.eventSpace_mono
    intro p hp hinj
    apply hne
    apply hinj
    simpa only [regroupTwo_label_first, regroupTwo_label_second] using hp
  have hb := ConnectedResolution.cross_collision_with_spectator
    (componentForest H r.val) (componentForest H s.val)
    (component_valid H hH r.val) (component_valid H hH s.val) i j
    (component_connected H r.val i) (component_connected H s.val j)
    hG hn hl hln B hB hBw (component_survival_budget H B hsmall r)
    (component_survival_budget H B hsmall s) (twoSpectatorSpace H S r s)
    Good hbad (U f) hf' hm'
  have hevent : (fun p : (LocalAssignment H r × LocalAssignment H s) × TwoSpectator H r s =>
      Collision H (vertexMap H r.val i) (vertexMap H s.val j) ((regroupTwo H r s hrs).symm p)) =
      (fun p => p.1.1 i = p.1.2 j) := by
    funext p
    apply propext
    constructor
    · intro hp
      simpa only [regroupTwo_label_first, regroupTwo_label_second] using hp.2
    · intro hp
      exact ⟨hne, by simpa only [regroupTwo_label_first, regroupTwo_label_second] using hp⟩
  have he := reindex_event_norm (regroupTwo H r s hrs)
    (Collision H (vertexMap H r.val i) (vertexMap H s.val j)) f
  rw [hevent] at he
  have hUf : reindex (regroupTwo H r s hrs) f = U f := by
    ext p
    rfl
  rw [hUf] at he
  rw [he]
  simpa only [U.norm_map] using hb

theorem pair_bound (H : AbsForest n) (hH : H.IsValid)
    (hG : G.IsValid) (hn : 16 ≤ n) (hl : 2 ≤ l) (hln : l ≤ n - 4)
    (B : Finset ℕ) (hB : Vbd n l ⊆ B) (hBw : Disjoint B (Vweld n))
    (hsmall : (H.k : ℝ) * (B.card : ℝ) * (4 / (2 : ℝ) ^ n) ≤ 1 / 2)
    (f : Hil (Fin H.k → Label n)) (hf : f ∈ coefficientSpace l G H B)
    (hm : f ∈ (coefficientSpace l G H B ⊓ (eventSpace Function.Injective)ᗮ)ᗮ)
    (a b : Fin H.k) :
    ‖(eventSpace (Collision H a b)).starProjection f‖ ^ 2 ≤
      2 * (H.k : ℝ) * (96 * ((n : ℝ) + 1) / (2 : ℝ) ^ n) * ‖f‖ ^ 2 := by
  obtain ⟨⟨r,i⟩,ha⟩ := (vertexSigma_bijective H).2 a
  obtain ⟨⟨s,j⟩,hb⟩ := (vertexSigma_bijective H).2 b
  change vertexMap H r.val i = a at ha
  change vertexMap H s.val j = b at hb
  rw [← ha, ← hb]
  by_cases hrs : r = s
  · subst s
    exact internal_pair_bound H hH hG hn hl hln B hB hBw hsmall r i j f hf hm
  · apply (cross_pair_bound H hH hG hn hl hln B hB hBw hsmall r s hrs i j f hf hm).trans
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    have hk : (1 : ℝ) ≤ (H.k : ℝ) := by
      have hk' : 1 ≤ H.k := by have := a.isLt; omega
      exact_mod_cast hk'
    have hn' : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
    have hp : (1 : ℝ) ≤ (H.k : ℝ) * ((n : ℝ) + 1) := one_le_mul_of_one_le_of_one_le hk hn'
    calc
      8 / (2 : ℝ) ^ n ≤ (2 * (H.k : ℝ) * (96 * ((n : ℝ) + 1))) / (2 : ℝ) ^ n := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        nlinarith
      _ = _ := by ring

end WeldedPath.Supplement.DisconnectedStability

end

-- Solutions.WeldedPathGlobalCollisionStability
section

namespace WeldedPath.Supplement.DisconnectedStability

open Classical FixedCollisions
open WeldedPath.WeightedCoefficients WeldedPath.CoefficientStability
open scoped BigOperators

variable {n : ℕ}

/-- Final finite pair union. All component and boundary-sector losses are
already accounted for in the pair estimate; no additional component count
is introduced here. -/
theorem stable_of_pair_bounds (H : AbsForest n)
    (S : Submodule ℂ (Hil (Fin H.k → Label n))) (δ : ℝ) (hδ : 0 ≤ δ)
    (hsmall : 2 * (H.k : ℝ) ^ 3 * δ ≤ 1 / 2)
    (hpair : ∀ f ∈ S, f ∈ (S ⊓ (eventSpace Function.Injective)ᗮ)ᗮ →
      ∀ a b : Fin H.k,
      ‖(eventSpace (Collision H a b)).starProjection f‖ ^ 2 ≤
        2 * (H.k : ℝ) * δ * ‖f‖ ^ 2)
    (f₀ : Hil (Fin H.k → Label n)) (hf₀ : f₀ ∈ S) :
    ∃! f : Hil (Fin H.k → Label n), f ∈ S ∧
      f ∈ (S ⊓ (eventSpace Function.Injective)ᗮ)ᗮ ∧
      (eventSpace Function.Injective).starProjection f =
        (eventSpace Function.Injective).starProjection f₀ ∧
      ‖f‖ ^ 2 ≤ 2 * ‖(eventSpace Function.Injective).starProjection f₀‖ ^ 2 := by
  apply stable_representative S (eventSpace Function.Injective) ?_ f₀ hf₀
  intro f hfS hf
  have he : (eventSpace (Function.Injective : (Fin H.k → Label n) → Prop))ᗮ =
      eventSpace (fun φ => ∃ p : Fin H.k × Fin H.k, Collision H p.1 p.2 φ) := by
    rw [eventSpace_orthogonal]
    congr 1
    funext φ
    exact propext (not_injective_iff_collision H φ)
  simp only [he]
  calc
    _ ≤ ∑ p : Fin H.k × Fin H.k, ‖(eventSpace (Collision H p.1 p.2)).starProjection f‖ ^ 2 :=
      event_union_norm_sq (fun p : Fin H.k × Fin H.k => Collision H p.1 p.2) f
    _ ≤ ∑ _p : Fin H.k × Fin H.k, 2 * (H.k : ℝ) * δ * ‖f‖ ^ 2 :=
      Finset.sum_le_sum (fun p _ => hpair f hfS hf p.1 p.2)
    _ = (2 * (H.k : ℝ) ^ 3 * δ) * ‖f‖ ^ 2 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_mul]
      ring
    _ ≤ (1 / 2 : ℝ) * ‖f‖ ^ 2 := mul_le_mul_of_nonneg_right hsmall (sq_nonneg _)

end WeldedPath.Supplement.DisconnectedStability

end

-- Solutions.WeldedPathDisconnectedStability
section

namespace WeldedPath.Supplement.DisconnectedStability

open Classical
open WeldedPath.WeightedCoefficients

variable {n l : ℕ} {G : WeldedInstance n}

/-- Stable coefficients for an arbitrary valid abstract forest, including
all connected components and all boundary-pattern sectors. The constant2
does not accumulate across components. -/
theorem disconnected_stable_representative (H : AbsForest n) (hH : H.IsValid)
    (hG : G.IsValid) (hn : 16 ≤ n) (hl : 2 ≤ l) (hln : l ≤ n - 4)
    (B : Finset ℕ) (hB : Vbd n l ⊆ B) (hBw : Disjoint B (Vweld n))
    (hsurvive : (H.k : ℝ) * (B.card : ℝ) * (4 / (2 : ℝ) ^ n) ≤ 1 / 2)
    (hcollision : 2 * (H.k : ℝ) ^ 3 *
      (96 * ((n : ℝ) + 1) / (2 : ℝ) ^ n) ≤ 1 / 2)
    (f₀ : Hil (Fin H.k → Label n)) (hf₀ : f₀ ∈ coefficientSpace l G H B) :
    ∃! f : Hil (Fin H.k → Label n), f ∈ coefficientSpace l G H B ∧
      f ∈ (coefficientSpace l G H B ⊓ (eventSpace Function.Injective)ᗮ)ᗮ ∧
      (eventSpace Function.Injective).starProjection f =
        (eventSpace Function.Injective).starProjection f₀ ∧
      ‖f‖ ^ 2 ≤ 2 * ‖(eventSpace Function.Injective).starProjection f₀‖ ^ 2 := by
  apply stable_of_pair_bounds H (coefficientSpace l G H B)
    (96 * ((n : ℝ) + 1) / (2 : ℝ) ^ n) (by positivity) hcollision
    ?_ f₀ hf₀
  intro f hf hm a b
  exact pair_bound H hH hG hn hl hln B hB hBw hsurvive f hf hm a b

end WeldedPath.Supplement.DisconnectedStability

end

-- Solutions.WeldedPathCanonicalStability
section

namespace WeldedPath.Supplement.DescriptionCoefficients

open Classical DisconnectedStability
open WeldedPath.WeightedCoefficients WeldedPath.HilbertSupport
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}

/-- Full coefficient stability in the span of the canonical descriptions,
for every valid forest, without a connectedness assumption. -/
theorem canonical_stable_representative (H : AbsForest n) (hH : H.IsValid)
    (hG : G.IsValid) (hn : 16 ≤ n) (hl : 2 ≤ l) (hln : l ≤ n - 4)
    (B : Finset ℕ) (hB : Vbd n l ⊆ B) (hBw : Disjoint B (Vweld n))
    (hsurvive : (H.k : ℝ) * (B.card : ℝ) * (4 / (2 : ℝ) ^ n) ≤ 1 / 2)
    (hcollision : 2 * (H.k : ℝ) ^ 3 *
      (96 * ((n : ℝ) + 1) / (2 : ℝ) ^ n) ≤ 1 / 2)
    (f₀ : Hil (Fin H.k → Label n)) (hf₀ : f₀ ∈ descriptionSpan l G H B) :
    ∃ f : Hil (Fin H.k → Label n), f ∈ descriptionSpan l G H B ∧
      (∀ φ, Function.Injective φ → f φ = f₀ φ) ∧
      ‖f‖ ^ 2 ≤ 2 * ∑ φ, if Function.Injective φ then ‖f₀ φ‖ ^ 2 else 0 := by
  have hS : coefficientSpace l G H B = descriptionSpan l G H B :=
    coefficientSpace_eq_descriptionSpan l G H hH B
  obtain ⟨f, ⟨hf, _, hp, hnrm⟩, _⟩ := disconnected_stable_representative H hH
    hG hn hl hln B hB hBw hsurvive hcollision f₀ (hS.symm ▸ hf₀)
  refine ⟨f, hS ▸ hf, ?_, ?_⟩
  · intro φ hφ
    have hh := congrArg (fun v : Hil (Fin H.k → Label n) => v φ) hp
    simpa only [eventSpace_projection, diagProj_apply, if_pos hφ] using hh
  · have he : ‖(eventSpace Function.Injective).starProjection f₀‖ ^ 2 =
        ∑ φ, if Function.Injective φ then ‖f₀ φ‖ ^ 2 else 0 := by
      rw [eventSpace_projection, EuclideanSpace.norm_sq_eq]
      apply Finset.sum_congr rfl
      intro φ _
      by_cases hφ : Function.Injective φ <;> simp [diagProj_apply, hφ]
    rwa [he] at hnrm

end WeldedPath.Supplement.DescriptionCoefficients

end

open Classical WeldedPath WeldedPath.Supplement
open scoped BigOperators

theorem solution :
    ∀ n l : ℕ, 16 ≤ n → 2 ≤ l → l ≤ n - 4 →
    ∀ G : WeldedInstance n, G.IsValid →
    ∀ H : AbsForest n, H.IsValid →
    ∀ B : Finset ℕ, Vbd n l ⊆ B → Disjoint B (Vweld n) →
      (H.k : ℝ) * (B.card : ℝ) * (4 / (2 : ℝ) ^ n) ≤ 1 / 2 →
      2 * (H.k : ℝ) ^ 3 * (96 * ((n : ℝ) + 1) / (2 : ℝ) ^ n) ≤ 1 / 2 →
    let amplitude := fun (sel : Finset (Fin H.k)) (φ₀ : Fin H.k → Label n) =>
      (WithLp.toLp 2 (fun φ : Fin H.k → Label n =>
        if (∀ s ∈ sel, H.Wfix φ s = H.Wfix φ₀ s) ∧
          (∀ s ∈ sel, ∀ u, H.graph.Reachable s u → u ∉ H.Ctree φ s → (φ u).val ∉ B)
        then (Real.sqrt (H.muRef l G φ) : ℂ) else 0) : Hil (Fin H.k → Label n))
    let S := Submodule.span ℂ {f | ∃ sel φ₀,
      (Description.mk H sel φ₀).IsValid ∧ f = amplitude sel φ₀}
    ∀ f₀ : Hil (Fin H.k → Label n), f₀ ∈ S →
    ∃ f : Hil (Fin H.k → Label n), f ∈ S ∧
      (∀ φ, Function.Injective φ → f φ = f₀ φ) ∧
      ‖f‖ ^ 2 ≤ 2 * ∑ φ, if Function.Injective φ then ‖f₀ φ‖ ^ 2 else 0 := by
  intro n l hn hl hln G hG H hH B hB hBw hsurvive hcollision
  let literal := fun (sel : Finset (Fin H.k)) (φ₀ : Fin H.k → Label n) =>
      (WithLp.toLp 2 (fun φ : Fin H.k → Label n =>
        if (∀ s ∈ sel, H.Wfix φ s = H.Wfix φ₀ s) ∧
          (∀ s ∈ sel, ∀ u, H.graph.Reachable s u → u ∉ H.Ctree φ s → (φ u).val ∉ B)
        then (Real.sqrt (H.muRef l G φ) : ℂ) else 0) : Hil (Fin H.k → Label n))
  let S := Submodule.span ℂ {f | ∃ sel φ₀,
    (Description.mk H sel φ₀).IsValid ∧ f = literal sel φ₀}
  change ∀ f₀ : Hil (Fin H.k → Label n), f₀ ∈ S →
    ∃ f : Hil (Fin H.k → Label n), f ∈ S ∧
      (∀ φ, Function.Injective φ → f φ = f₀ φ) ∧
      ‖f‖ ^ 2 ≤ 2 * ∑ φ, if Function.Injective φ then ‖f₀ φ‖ ^ 2 else 0
  have he (sel : Finset (Fin H.k)) (φ₀ : Fin H.k → Label n) :
      DescriptionCoefficients.amplitude l G H B sel φ₀ = literal sel φ₀ := by
    ext φ
    change (Real.sqrt (if (∀ s ∈ sel, H.Wfix φ s = H.Wfix φ₀ s) ∧
        (∀ s ∈ sel, ∀ u, H.graph.Reachable s u → u ∉ H.Ctree φ s → (φ u).val ∉ B)
      then H.muRef l G φ else 0) : ℂ) = _
    by_cases h : (∀ s ∈ sel, H.Wfix φ s = H.Wfix φ₀ s) ∧
        (∀ s ∈ sel, ∀ u, H.graph.Reachable s u → u ∉ H.Ctree φ s → (φ u).val ∉ B)
    · simp only [literal, PiLp.toLp_apply, if_pos h]
    · simp only [literal, PiLp.toLp_apply, if_neg h, Real.sqrt_zero, Complex.ofReal_zero]
  have hS : DescriptionCoefficients.descriptionSpan l G H B = S := by
    unfold DescriptionCoefficients.descriptionSpan S
    congr 1
    ext f
    constructor
    · rintro ⟨sel, φ₀, hD, rfl⟩
      exact ⟨sel, φ₀, hD, he sel φ₀⟩
    · rintro ⟨sel, φ₀, hD, rfl⟩
      exact ⟨sel, φ₀, hD, (he sel φ₀).symm⟩
  intro f₀ hf₀
  obtain ⟨f, hf, heq, hnrm⟩ := DescriptionCoefficients.canonical_stable_representative
    H hH hG hn hl hln B hB hBw hsurvive hcollision f₀ (hS.symm ▸ hf₀)
  exact ⟨f, hS ▸ hf, heq, hnrm⟩
