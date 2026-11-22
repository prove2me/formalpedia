-- Prove2me | solution 1 for WeldedPath.Supplement.boundary_coefficient_comparison
-- status  : ACCEPTED   (prove)
-- author  : @dmilosch
-- created : 2026-11-22T18:21:11.337497+00:00
-- url     : https://prove2.me/submissions/1b904242-328e-4caa-801c-1f56d5752fdd

import Definitions.Def_WeldedPath_InjDb
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Algebra.Order.Chebyshev
import Definitions.Def_WeldedPath_Supplement_projGood
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Prod.Lex
import Mathlib.Tactic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Prod
import Definitions.Def_WeldedPath_Supplement_pCross
import Definitions.Def_WeldedPath_bEdge
import Definitions.Def_WeldedPath_Nb
import Definitions.Def_WeldedPath_Supplement_pWt
import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp
import Definitions.Def_WeldedPath_cpO
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Definitions.Def_WeldedPath_exactCpO
import Definitions.Def_WeldedPath_Supplement_exactCpWT
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Definitions.Def_WeldedPath_opTensor
import Mathlib.Analysis.CStarAlgebra.Basic

set_option autoImplicit false

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




theorem opTensor_ket [DecidableEq A] [DecidableEq X]
    {B : Type*} [Fintype B] (S : Hil A →L[ℂ] Hil B) (T : Hil X →L[ℂ] Hil Y)
    (a : A) (x : X) :
    opTensor S T (ket (a, x)) = ketTensor (S (ket a)) (T (ket x)) := by
  simp [opTensor, ketBra_apply, inner_ket, ket_apply]




end WeldedPath.HilbertSupport

end

section

namespace WeldedPath.UniformFiberEncoding

open Classical
open scoped BigOperators

variable {A B : Type*} [Fintype A] [Fintype B]








end WeldedPath.UniformFiberEncoding

end

section

namespace WeldedPath.UniformFiberEncoding

open Classical
open scoped BigOperators

variable {A B : Type*} [Fintype A] [Fintype B]


end WeldedPath.UniformFiberEncoding

end

section

namespace WeldedPath.UniformFiberEncoding

open Classical
open scoped BigOperators

variable {A B : Type*} [Fintype A] [Fintype B]


end WeldedPath.UniformFiberEncoding

end

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




end WeldedPath.Supplement.FixedData

end

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

section

/-! Finite weighted laws split by a separator.  All identities also cover zero
normalizers: division is the ordinary totalized division on `ℝ`. -/

namespace FiniteWeightedForest

open scoped BigOperators

section ProductLaws

variable {Ω A B : Type*} [Fintype Ω] [Fintype A] [Fintype B]







end ProductLaws

section VertexPartition

variable {V X : Type*} [Fintype V] [DecidableEq V] [Fintype X]





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



end EdgeProducts

end FiniteWeightedForest

end

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



end ForestCuts

end FiniteWeightedForest

end

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




end WeldedPath.Supplement.ForestFactorization

end

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



end WeldedPath.Supplement.ForestFactorization

end

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






noncomputable def extendComponent (H : AbsForest n) (s : Fin H.k)
    (z : H.comp s → Label n) (u : Fin H.k) : Label n :=
  if hu : u ∈ H.comp s then z ⟨u, hu⟩ else 0

@[simp] theorem extendComponent_on (H : AbsForest n) (s : Fin H.k)
    (z : H.comp s → Label n) (u : H.comp s) : extendComponent H s z u = z u := by
  simp only [extendComponent, dif_pos u.property]




end WeldedPath.Supplement.ComponentRestriction

end

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

section

namespace WeldedPath.Supplement.CrossingExclusion

open WeldedInstance InjDb
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}



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








end WeldedPath.Supplement.CrossingExclusion

end

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


end WeldedPath.Supplement.ConnectedReference

end

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


theorem muRef_eq_product_restrictions (l : ℕ) (G : WeldedInstance n) (H : AbsForest n)
    (hH : H.IsValid) (φ : Fin H.k → Label n) :
    H.muRef l G φ = ∏ s ∈ Finset.univ.filter H.IsCompRoot,
      (componentForest H s).muRef l G (restrict H s φ) := by
  apply Finset.prod_congr rfl
  intro s _
  exact (muRef_restrict_eq l G H hH s φ).symm

end WeldedPath.Supplement.ComponentForest

end

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


end WeldedPath.Supplement.FixedDataSeparator

end

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


end WeldedPath.Supplement.BoundaryCoefficients

end

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



theorem wfix_eq_on_nonweld_edge (H : AbsForest n) (hH : H.IsValid)
    (e : Fin H.k × Fin H.k) (he : e ∈ H.E) (φ : Fin H.k → Label n)
    (hw : ¬H.IsWeldUnder φ e) : H.Wfix φ e.1 = H.Wfix φ e.2 := by
  have hr : (H.treeGraph φ).Reachable e.1 e.2 :=
    SimpleGraph.Adj.reachable ⟨ne_of_lt (hH.1 e he), Or.inl ⟨he, hw⟩⟩
  have hm : e.1 ∈ H.Ctree φ e.2 :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr.symm⟩
  exact (BoundaryCoefficients.wfix_eq_of_mem H φ e.1 e.2 hm).symm




end WeldedPath.Supplement.FixedDataFunctions

end

section

namespace WeldedPath.Supplement.ComponentForest

open Classical ComponentRestriction FixedDataFunctions

variable {n : ℕ}








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

section

namespace WeldedPath.Supplement.ComponentForest

open Classical QAlgorithms HilbertSupport
open scoped BigOperators

variable {n : ℕ}

section Generic

variable {I : Type*} [Fintype I] [DecidableEq I]







theorem prod_one {M : Type*} [CommMonoid M] (f : I → M) (a : I) :
    (∏ i, f i) = f a * ∏ i : {i : I // i ≠ a}, f i.val := by
  rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ a)]
  congr 1
  exact Finset.prod_subtype _ (fun i => by simp only [Finset.mem_erase,
    Finset.mem_univ, and_true]) f



end Generic

abbrev LocalAssignment (H : AbsForest n) (s : Roots H) :=
  Fin (H.comp s.val).card → Label n

@[simp] theorem assignmentEquiv_restrict (H : AbsForest n) (φ : Fin H.k → Label n)
    (s : Roots H) : assignmentEquiv H φ s = restrict H s.val φ := rfl

abbrev OneSpectator (H : AbsForest n) (a : Roots H) :=
  (s : {s : Roots H // s ≠ a}) → LocalAssignment H s.val


noncomputable def regroupOne (H : AbsForest n) (a : Roots H) :
    (Fin H.k → Label n) ≃ LocalAssignment H a × OneSpectator H a :=
  (assignmentEquiv H).trans (Equiv.piSplitAt a (LocalAssignment H))





@[simp] theorem regroupOne_restrict_first (H : AbsForest n) (a : Roots H)
    (p : LocalAssignment H a × OneSpectator H a) :
    restrict H a.val ((regroupOne H a).symm p) = p.1 :=
  congrArg Prod.fst ((regroupOne H a).apply_symm_apply p)

@[simp] theorem regroupOne_restrict_rest (H : AbsForest n) (a : Roots H)
    (p : LocalAssignment H a × OneSpectator H a) (s : {s : Roots H // s ≠ a}) :
    restrict H s.val.val ((regroupOne H a).symm p) = p.2 s :=
  congrArg (fun q => q.2 s) ((regroupOne H a).apply_symm_apply p)




noncomputable def regroupOneHil (H : AbsForest n) (a : Roots H) :
    Hil (Fin H.k → Label n) ≃ₗᵢ[ℂ] Hil (LocalAssignment H a × OneSpectator H a) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (regroupOne H a)


@[simp] theorem regroupOneHil_apply (H : AbsForest n) (a : Roots H)
    (f : Hil (Fin H.k → Label n)) (p : LocalAssignment H a × OneSpectator H a) :
    regroupOneHil H a f p = f ((regroupOne H a).symm p) := rfl




noncomputable def productAmplitude (H : AbsForest n)
    (f : (s : Roots H) → Hil (LocalAssignment H s)) : Hil (Fin H.k → Label n) :=
  WithLp.toLp 2 (fun φ => ∏ s : Roots H, f s (restrict H s.val φ))


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


end WeldedPath.Supplement.ComponentForest

end

section

namespace WeldedPath.CoefficientStability

open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]






end WeldedPath.CoefficientStability

end

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

section

namespace WeldedPath.ProductDecomposition

open Classical HilbertSupport WeightedCoefficients
open scoped BigOperators

variable {X Y Z ι κ : Type*} [Fintype X] [Fintype Y] [Fintype ι] [Fintype κ]
  [DecidableEq X] [DecidableEq Y]




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


end WeldedPath.ProductDecomposition

end

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


end WeldedPath.WeightedCoefficients

end

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


end WeldedPath.WeightedCoefficients

namespace WeldedPath.Supplement

noncomputable def localCoefficientSpace {n : ℕ} (H : AbsForest n)
    (μ : (Fin H.k → Label n) → ℝ) (v : Fin H.k) :
    Submodule ℂ (Hil (Fin H.k → Label n)) :=
  WeightedCoefficients.dataSpace μ (fun φ => H.Wfix φ v)

end WeldedPath.Supplement

end

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



end WeldedPath.ProductDecomposition

end

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


end WeldedPath.CoefficientStability

end

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










end WeldedPath.ProductDecomposition

end

section

namespace WeldedPath.ProductDecomposition

open Classical HilbertSupport WeightedCoefficients
open scoped BigOperators

variable {X Y A B Z : Type*} [Fintype X] [Fintype Y]
  [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B]



end WeldedPath.ProductDecomposition

end

section

namespace WeldedPath.ProductDecomposition

open Classical HilbertSupport WeightedCoefficients
open scoped BigOperators

variable {X Y A B Z : Type*} [Fintype X] [Fintype Y]
  [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B]



end WeldedPath.ProductDecomposition

end

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




end WeldedPath.ProductDecomposition

end

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

section

namespace WeldedPath.Supplement.ComponentForest

open Classical QAlgorithms HilbertSupport ProductDecomposition
open scoped BigOperators

variable {n : ℕ}




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

section

namespace WeldedPath.LoopProof

open WeldedInstance










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







end WeldedPath.LoopProof

end

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





lemma kappa_propagates_point_bound (hG : G.IsValid) (α : Fin 3)
    (p : Label n → ℝ) (M : ℝ) (hM : 0 ≤ M) (hp : ∀ x, p x ≤ M) (y : ℕ) :
    (∑ x : Label n, p x * kappa l G α x.1 y) ≤ M :=
  finite_kernel_point_bound (fun x : Label n => kappa l G α x.1)
    (fun x y => kappa_nonneg l G α x.1 y)
    (fun y => kappa_label_column_sum_le_one hG α y) p M hM hp y


end WeldedPath.Supplement.KappaKernel

end

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



/-- The unnormalized description law before removing collisions. -/
noncomputable def descriptionWeight (l : ℕ) (G : WeldedInstance n) (B : Finset ℕ)
    (D : Description n) (φ : Fin D.H.k → Label n) : ℝ :=
  if (∀ s ∈ D.sel, D.H.Wfix φ s = D.H.Wfix D.ϕ₀ s) ∧
      (∀ s ∈ D.sel, ∀ u, D.H.graph.Reachable s u →
        u ∉ D.H.Ctree φ s → (φ u).val ∉ B)
  then D.H.muRef l G φ else 0



end WeldedPath.Supplement.ForestFactorization

end

section

namespace WeldedPath.Supplement.ComponentForest

open Classical ForestFactorization FixedDataFunctions
open scoped BigOperators

variable {n : ℕ}





end WeldedPath.Supplement.ComponentForest

end

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


end WeldedPath.Supplement.DescriptionCoefficients

end

section

namespace WeldedPath.CollisionStability

open scoped BigOperators
open Classical WeightedCoefficients CoefficientStability HilbertSupport

variable {Ω D ι χ : Type*} [Fintype Ω] [DecidableEq Ω]
  [Fintype ι] [Fintype χ] [DecidableEq D]






end WeldedPath.CollisionStability

end

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


end WeldedPath.WeldClasses

end

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



end WeldedPath.NearWeldClasses

end

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


end WeldedPath.Supplement.FirstFreeStep

end

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


noncomputable def step (l : ℕ) (G : WeldedInstance n) (α : Fin 3)
    (p : Label n → ℝ) : Label n → ℝ := fun y =>
  ∑ x : Label n, p x * kappa l G α x.1 y.1
















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



end WeldedPath.Supplement.KappaWalk

end

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




end FiniteWeightedForest

end

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


end WeldedPath.Supplement.ReciprocalClasses

end

section

namespace WeldedPath.Supplement.BranchCollision

open scoped BigOperators
open Classical KappaKernel KappaWalk ReciprocalClasses

variable {n l : ℕ} {G : WeldedInstance n}

















end WeldedPath.Supplement.BranchCollision

end

section

namespace WeldedPath.Supplement.ForestCollision

open KappaForest KappaKernel KappaWalk BranchCollision
open scoped BigOperators

variable {X : Type*} [Fintype X] {m : ℕ}






variable {n l : ℕ} {G : WeldedInstance n}










end WeldedPath.Supplement.ForestCollision

end

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


end WeldedPath.Supplement.ConnectedConcentration

end

section

namespace WeldedPath.Supplement.ConditionalInjectivity

open Classical ConnectedConcentration
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}









end WeldedPath.Supplement.ConditionalInjectivity

end

section

namespace WeldedPath.Supplement.FixedCollisions

open scoped BigOperators
open Classical WeldedPath.WeightedCoefficients WeldedPath.HilbertSupport

variable {n : ℕ}




lemma sfix_eq_of_wfix_eq (H : AbsForest n) (hH : H.IsValid)
    (v : Fin H.k) (φ ψ : Fin H.k → Label n) (hd : H.Wfix φ v = H.Wfix ψ v) :
    H.Sfix φ v = H.Sfix ψ v :=
  FixedData.sfix_eq_of_agree_sfix H hH φ ψ v
    ((FixedData.wfix_eq_iff_agree_sfix H hH φ ψ v).mp hd)


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







end WeldedPath.Supplement.FixedCollisions

end

section

namespace WeldedPath.Supplement.SourceFiberBound

open Classical ConnectedConcentration FixedData
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}



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


end WeldedPath.Supplement.BoundarySector

end

section

namespace FiniteWeightedForest

open scoped BigOperators
open Classical


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



end FiniteWeightedForest

end

section

namespace WeldedPath.Supplement.ForestFactorization

open scoped BigOperators
open FiniteWeightedForest
open Classical

variable {n : ℕ}







end WeldedPath.Supplement.ForestFactorization

end

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


end WeldedPath.Supplement.EdgeCoefficientSplit

end

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



end WeldedPath.Supplement.FiberCollision

end

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




end WeldedPath.CoefficientStability

end

section

namespace WeldedPath.Supplement.CoefficientDecomposition

open Classical CoefficientOrder EdgeCoefficientSplit FixedDataFunctions
open WeldedPath.WeightedCoefficients WeldedPath.CoefficientStability
open scoped BigOperators

variable {n : ℕ}


end WeldedPath.Supplement.CoefficientDecomposition

end

section

namespace WeldedPath.Supplement.StableCoefficients

open scoped BigOperators
open Classical FixedCollisions FiberCollision FixedDataFunctions
open WeldedPath.WeightedCoefficients WeldedPath.CollisionStability

variable {n l : ℕ} {G : WeldedInstance n}


end WeldedPath.Supplement.StableCoefficients

end

section

namespace WeldedPath.SectorStability

open scoped BigOperators
open Classical WeightedCoefficients CoefficientStability HilbertSupport

variable {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype ι]




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




end WeldedPath.SectorStability

end

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


end WeldedPath.Supplement.AllBoundaryStability

end

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


end WeldedPath.Supplement.DescriptionCoefficients

end

section

namespace WeldedPath.CompressedPrimitive

open Classical InjDb
open scoped BigOperators ComplexConjugate

















end WeldedPath.CompressedPrimitive

end

section

namespace WeldedPath.CompressedPrimitive

open Classical InjDb
open scoped BigOperators ComplexConjugate










end WeldedPath.CompressedPrimitive

end

section

namespace WeldedPath.CompressedPrimitive

open Classical InjDb HilbertSupport
open scoped BigOperators ComplexConjugate

variable {s : ℕ}






end WeldedPath.CompressedPrimitive

end

section

namespace WeldedPath.CompletionLevels

open Classical InjDb
open scoped BigOperators

variable {s : ℕ}















end WeldedPath.CompletionLevels

end

section

namespace WeldedPath.EncodedOracleUnitary

open Classical QAlgorithms HilbertSupport CompressedPrimitive Supplement
open scoped BigOperators

variable {X Y A : Type*} [Fintype X] [Fintype Y] [Fintype A]
















end WeldedPath.EncodedOracleUnitary

end

section

namespace WeldedPath.ControlledOperators

open Classical HilbertSupport EncodedOracleUnitary
open scoped BigOperators

variable {C X Y : Type*} [Fintype C] [Fintype X] [Fintype Y]
  [DecidableEq C] [DecidableEq X]




end WeldedPath.ControlledOperators

end

section

namespace WeldedPath.CompressedPrimitive

open Classical InjDb HilbertSupport CoefficientStability
open scoped BigOperators ComplexConjugate

variable {s : ℕ}















end WeldedPath.CompressedPrimitive

end

section

namespace WeldedPath.Supplement.LabelBookkeeping

open Classical DescriptionCoefficients CompressedPrimitive InjDb
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}

















end WeldedPath.Supplement.LabelBookkeeping

end

section

namespace WeldedPath.Supplement.LabelBookkeeping

open Classical CompressedPrimitive
open scoped BigOperators

variable {n : ℕ}



















end WeldedPath.Supplement.LabelBookkeeping

end

section

namespace WeldedPath.Supplement.LabelBookkeeping

open Classical ForestFactorization FiniteWeightedForest
open scoped BigOperators

variable {n : ℕ}


















end WeldedPath.Supplement.LabelBookkeeping

end

section

namespace WeldedPath.Supplement.EdgeBookkeeping

open Classical LabelBookkeeping

variable {n : ℕ}



def FreshColor (H : AbsForest n) (a : Fin H.k) (α : Fin 3) : Prop :=
  ∀ p ∈ H.E,p.1 = a ∨ p.2 = a → H.color p ≠ α













end WeldedPath.Supplement.EdgeBookkeeping

end

section

namespace WeldedPath.Supplement.AssignmentDatabase

open Classical KappaKernel KappaWalk

variable {n l : ℕ} {G : WeldedInstance n}
























end WeldedPath.Supplement.AssignmentDatabase

end

section

namespace WeldedPath.Supplement.DatabaseReadout

open Classical AssignmentDatabase

variable {n l : ℕ} {G : WeldedInstance n}









end WeldedPath.Supplement.DatabaseReadout

end

section

namespace WeldedPath.Supplement.DatabaseSupport

open Classical AssignmentDatabase

variable {n l : ℕ} {G : WeldedInstance n}






noncomputable def assignmentEquiv {A B X : Type*} (φ : A → X) (ψ : B → X)
    (hφ : Function.Injective φ) (hψ : Function.Injective ψ) (hr : Set.range φ = Set.range ψ) :
    A ≃ B :=
  ((Equiv.ofInjective φ hφ).trans (Equiv.setCongr hr)).trans (Equiv.ofInjective ψ hψ).symm






end WeldedPath.Supplement.DatabaseSupport

end

section

namespace WeldedPath.Supplement.DatabaseSupport

open Classical AssignmentDatabase

variable {n l : ℕ} {G : WeldedInstance n}

def ColoredAdj (H : AbsForest n) (u v : Fin H.k) (α : Fin 3) : Prop :=
  ∃ p ∈ H.E, (p = (u, v) ∨ p = (v, u)) ∧ H.color p = α

def IsForestIso (H K : AbsForest n) (e : Fin H.k ≃ Fin K.k) : Prop :=
  (∀ u, K.lab (e u) = H.lab u) ∧
    ∀ u v α, ColoredAdj H u v α ↔ ColoredAdj K (e u) (e v) α






theorem IsForestIso.symm (H K : AbsForest n) (e : Fin H.k ≃ Fin K.k)
    (h : IsForestIso H K e) : IsForestIso K H e.symm := by
  constructor
  · intro u
    simpa only [Equiv.apply_symm_apply] using (h.1 (e.symm u)).symm
  · intro u v α
    simpa only [Equiv.apply_symm_apply] using (h.2 (e.symm u) (e.symm v) α).symm






end WeldedPath.Supplement.DatabaseSupport

end

section

namespace WeldedPath.Supplement.DatabaseReadout

open Classical AssignmentDatabase KappaKernel DatabaseSupport

variable {n l : ℕ} {G : WeldedInstance n}









end WeldedPath.Supplement.DatabaseReadout

end

section

namespace WeldedPath.Supplement.AssignmentDatabase

open Classical KappaKernel

variable {n l : ℕ} {G : WeldedInstance n}






end WeldedPath.Supplement.AssignmentDatabase

end

section

namespace WeldedPath.Supplement.EdgeBookkeeping

open Classical LabelBookkeeping AssignmentDatabase DatabaseReadout
open WeldedPath.CompressedPrimitive InjDb

variable {n l : ℕ} {G : WeldedInstance n}








end WeldedPath.Supplement.EdgeBookkeeping

end

section

namespace WeldedPath.Supplement.EdgeBookkeeping

open Classical LabelBookkeeping AssignmentDatabase KappaKernel ForestFactorization
open FiniteWeightedForest WeldedPath.WeightedCoefficients
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}








end WeldedPath.Supplement.EdgeBookkeeping

end

section

namespace WeldedPath.Supplement.DatabaseSupport

open Classical ForestFactorization FiniteWeightedForest

variable {n l : ℕ} {G : WeldedInstance n}













end WeldedPath.Supplement.DatabaseSupport

end

section

namespace WeldedPath.Supplement.DatabaseSupport

open Classical

variable {n : ℕ}

lemma tree_adj_iff (H : AbsForest n) (φ : Fin H.k → Label n) (u v : Fin H.k) :
    (H.treeGraph φ).Adj u v ↔
      H.graph.Adj u v ∧ ¬ ((φ u).val ∈ Vweld n ∧ (φ v).val ∈ Vweld n) := by
  change (u ≠ v ∧ (((u,v) ∈ H.E ∧ ¬ _) ∨ ((v,u) ∈ H.E ∧ ¬ _))) ↔ _
  simp only [AbsForest.IsWeldUnder]
  change (u ≠ v ∧ (((u,v) ∈ H.E ∧ ¬ _) ∨ ((v,u) ∈ H.E ∧ ¬ _))) ↔
    (u ≠ v ∧ ((u,v) ∈ H.E ∨ (v,u) ∈ H.E)) ∧ ¬ _
  tauto






end WeldedPath.Supplement.DatabaseSupport

end

section

namespace WeldedPath.Supplement.LabelBookkeeping

open Classical DatabaseSupport

variable {n : ℕ}













end WeldedPath.Supplement.LabelBookkeeping

end

section

namespace WeldedPath.Supplement.EdgeBookkeeping

open Classical LabelBookkeeping DatabaseSupport

variable {n : ℕ}






















end WeldedPath.Supplement.EdgeBookkeeping

end

section

namespace WeldedPath.Supplement.EdgeBookkeeping

open Classical LabelBookkeeping ForestFactorization

variable {n : ℕ}








end WeldedPath.Supplement.EdgeBookkeeping

end

section

namespace WeldedPath.Supplement.LabelBookkeeping

open Classical AssignmentDatabase

variable {n l : ℕ} {G : WeldedInstance n}







end WeldedPath.Supplement.LabelBookkeeping

end

section

namespace WeldedPath.RegisterTransport

open Classical Supplement HilbertSupport EncodedOracleUnitary ControlledOperators
open scoped BigOperators

variable {Ω C X : Type*} [Fintype Ω] [Fintype C] [Fintype X]
  [DecidableEq Ω] [DecidableEq C] [DecidableEq X]








end WeldedPath.RegisterTransport

end

section

namespace WeldedPath.Supplement.DatabaseSupport

open Classical AssignmentDatabase

variable {n l : ℕ} {G : WeldedInstance n}

abbrev ForestAut (H : AbsForest n) := {e : Fin H.k ≃ Fin H.k // IsForestIso H H e}

def AssignmentFiber (l : ℕ) (G : WeldedInstance n) (H : AbsForest n) (I : Db l G) :=
  {φ : Fin H.k → Label n // Function.Injective φ ∧ H.muRef l G φ ≠ 0 ∧ H.IsDbOf l G φ I}

noncomputable instance (H : AbsForest n) : Fintype (ForestAut H) := inferInstance


noncomputable instance (H : AbsForest n) (I : Db l G) : Fintype (AssignmentFiber l G H I) :=
  inferInstanceAs (Fintype {φ : Fin H.k → Label n //
    Function.Injective φ ∧ H.muRef l G φ ≠ 0 ∧ H.IsDbOf l G φ I})







end WeldedPath.Supplement.DatabaseSupport

end

section

namespace WeldedPath.Supplement.DatabaseSupport

open Classical AssignmentDatabase

variable {n l : ℕ} {G : WeldedInstance n}

def SupportedAssignment (l : ℕ) (G : WeldedInstance n) (H : AbsForest n) :=
  {φ : Fin H.k → Label n // Function.Injective φ ∧ H.muRef l G φ ≠ 0}

noncomputable instance (H : AbsForest n) : Fintype (SupportedAssignment l G H) :=
  inferInstanceAs (Fintype {φ : Fin H.k → Label n // Function.Injective φ ∧ H.muRef l G φ ≠ 0})


















end WeldedPath.Supplement.DatabaseSupport

end

section

namespace WeldedPath.Supplement.LabelBookkeeping

open Classical ForestFactorization

variable {n : ℕ}








end WeldedPath.Supplement.LabelBookkeeping

end

section

namespace WeldedPath.Supplement.LabelBookkeeping

open Classical DescriptionCoefficients

variable {n l : ℕ} {G : WeldedInstance n}


end WeldedPath.Supplement.LabelBookkeeping

end

section

namespace WeldedPath.Supplement.LabelInsertion

open Classical LabelBookkeeping AssignmentDatabase DatabaseSupport RegisterTransport
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}













end WeldedPath.Supplement.LabelInsertion

end

section

namespace WeldedPath.Supplement.LabelInsertion

open Classical LabelBookkeeping AssignmentDatabase DatabaseSupport
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}








end WeldedPath.Supplement.LabelInsertion

end

section

namespace WeldedPath.Supplement.LabelInsertion

open Classical LabelBookkeeping AssignmentDatabase DatabaseSupport
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}











end WeldedPath.Supplement.LabelInsertion

end

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

section

namespace WeldedPath.CoefficientStability

open scoped BigOperators

variable {E Θ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]


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


end WeldedPath.Supplement.CoefficientDecomposition

end

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


end WeldedPath.Supplement.CoefficientDecomposition

end

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



end WeldedPath.Supplement.AnchoredLinearSplit

end

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


end WeldedPath.Supplement.AllSectorLinear

end

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


end WeldedPath.Supplement.CoefficientDecomposition

end

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


end WeldedPath.Supplement.ConnectedResolution

end

section

namespace WeldedPath.ProductDecomposition

open Classical HilbertSupport WeightedCoefficients CoefficientStability
open scoped BigOperators

variable {X Y ι : Type*} [Fintype X] [Fintype Y] [Fintype ι]
  [DecidableEq X] [DecidableEq Y]



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




end WeldedPath.ProductDecomposition

end

section

/- Module: WeldedPathEdgePotential -/
section

namespace WeldedPath.Supplement.EdgePotential

open Classical KappaKernel ReciprocalClasses FirstFreeStep
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}

/-- The loss charged to an edge query: a boundary endpoint or any of the
`k` vertices already represented by the abstract forest. -/
noncomputable def potential (l : ℕ) (G : WeldedInstance n) (α : Fin 3)
    (B : Finset ℕ) (k : ℕ) (x : Label n) : ℝ :=
  (∑ y ∈ B,kappa l G α x.val y) + (k : ℝ) * firstEdgeCap (l := l) G α x.val

theorem potential_nonneg (α : Fin 3) (B : Finset ℕ) (k : ℕ) (x : Label n) :
    0 ≤ potential l G α B k x :=
  add_nonneg (Finset.sum_nonneg (fun _ _ => kappa_nonneg _ _ _ _ _))
    (mul_nonneg (Nat.cast_nonneg _) (firstEdgeCap_nonneg G α x.val))

theorem potential_sum_le (hG : G.IsValid) (hln : l ≤ n)
    (α : Fin 3) (B : Finset ℕ) (k : ℕ) :
    (∑ x : Label n,potential l G α B k x) ≤
      (B.card : ℝ) + 12 * (k : ℝ) * ((n : ℝ)+1) := by
  have hb : (∑ x : Label n,∑ y ∈ B,kappa l G α x.val y) ≤ (B.card : ℝ) := by
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ y ∈ B,(1 : ℝ) := Finset.sum_le_sum fun y _ =>
        kappa_label_column_sum_le_one hG α y
      _ = _ := by simp
  have hc := firstEdgeCap_sum_le G hln α
  unfold potential
  rw [Finset.sum_add_distrib,← Finset.mul_sum]
  have hh := mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  nlinarith

theorem firstEdgeCap_weld_le (hG : G.IsValid) (hn : 2 ≤ n) (hl : 1 ≤ l)
    (α : Fin 3) {u : ℕ} (hu : u ∈ Vweld n) :
    firstEdgeCap (l := l) G α u ≤ 4 / (2 : ℝ)^n := by
  cases hp : permData l G u α with
  | none => simp only [firstEdgeCap,hp]; positivity
  | some d =>
    obtain ⟨b,e,t⟩ := d
    have he := KappaKernel.eAlpha_spec (permData_eAlpha hp)
    have hc := class_card_ge_of_incident_weld hG hn hl e.property he.2.2 hu
    simpa only [firstEdgeCap,hp,classSize] using NearWeldClasses.reciprocal_le_four_dyadic hn hc

theorem potential_weld_le (hG : G.IsValid) (hn : 2 ≤ n) (hl : 1 ≤ l)
    (α : Fin 3) (B : Finset ℕ) (k : ℕ) (x : Label n) (hx : x.val ∈ Vweld n) :
    potential l G α B k x ≤ 4 * ((B.card : ℝ)+(k : ℝ)) / (2 : ℝ)^n := by
  have hb : (∑ y ∈ B,kappa l G α x.val y) ≤ (B.card : ℝ) * (4 / (2 : ℝ)^n) := by
    calc
      _ ≤ ∑ _y ∈ B,4 / (2 : ℝ)^n :=
        Finset.sum_le_sum fun y _ => kappa_from_weld_le hG hn hl hx α y
      _ = _ := by simp
  have hc := mul_le_mul_of_nonneg_left (firstEdgeCap_weld_le hG hn hl α hx)
    (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  change _ + _ ≤ _
  calc
    _ ≤ (B.card : ℝ) * (4 / (2 : ℝ)^n) + (k : ℝ) * (4 / (2 : ℝ)^n) := add_le_add hb hc
    _ = _ := by ring




end WeldedPath.Supplement.EdgePotential
end

/- Module: WeldedPathFiberPotential -/
section

namespace WeldedPath.WeightedCoefficients

open Classical Supplement.FixedDataFunctions
open scoped BigOperators

variable {Ω D X : Type*} [Fintype Ω] [Fintype X]

theorem fiber_point_potential_bound (μ : Ω → ℝ) (data : Ω → D) (a : Ω → X)
    (Free : Ω → Prop) (p : X → ℝ) (hp : ∀ x,0 ≤ p x) (ε : ℝ)
    (hcap : ∀ d x,(∑ ω,if data ω = d ∧ Free ω ∧ a ω = x then μ ω else 0) ≤
      ε * ∑ ω,if data ω = d then μ ω else 0) (d : D) :
    (∑ ω,if data ω = d ∧ Free ω then μ ω * p (a ω) else 0) ≤
      ε * (∑ x,p x) * ∑ ω,if data ω = d then μ ω else 0 := by
  calc
    _ = ∑ x,p x * ∑ ω,if data ω = d ∧ Free ω ∧ a ω = x then μ ω else 0 := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro ω _
      by_cases hd : data ω = d <;> by_cases hf : Free ω <;>
        simp [hd,hf,mul_ite,mul_comm]
    _ ≤ ∑ x,p x * (ε * ∑ ω,if data ω = d then μ ω else 0) :=
      Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hcap d x) (hp x)
    _ = _ := by rw [← Finset.sum_mul]; ring

theorem fiber_potential_bound_with_fixed (μ : Ω → ℝ) (hμ : ∀ ω,0 ≤ μ ω)
    (data : Ω → D) (a : Ω → X) (Free E : Ω → Prop)
    (p : X → ℝ) (hp : ∀ x,0 ≤ p x) (ε W : ℝ) (hW : 0 ≤ W)
    (hcap : ∀ d x,(∑ ω,if data ω = d ∧ Free ω ∧ a ω = x then μ ω else 0) ≤
      ε * ∑ ω,if data ω = d then μ ω else 0)
    (hfixed : ∀ ω,E ω → ¬ Free ω → p (a ω) ≤ W) (d : D) :
    (∑ ω,if data ω = d ∧ E ω then μ ω * p (a ω) else 0) ≤
      (ε * (∑ x,p x) + W) * ∑ ω,if data ω = d then μ ω else 0 := by
  calc
    _ ≤ (∑ ω,if data ω = d ∧ Free ω then μ ω * p (a ω) else 0) +
        W * ∑ ω,if data ω = d then μ ω else 0 := by
      rw [Finset.mul_sum,← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro ω _
      by_cases hd : data ω = d
      · by_cases he : E ω
        · by_cases hf : Free ω
          · simp only [hd,he,hf,and_self,if_true]
            exact le_add_of_nonneg_right (mul_nonneg hW (hμ ω))
          · simp only [hd,he,hf,true_and,and_self,if_true,if_false,add_zero,zero_add]
            simpa only [mul_comm W] using mul_le_mul_of_nonneg_left (hfixed ω he hf) (hμ ω)
        · simp only [hd,he,and_false,if_false,true_and,if_true]
          apply add_nonneg
          · split_ifs; exact mul_nonneg (hμ ω) (hp _); rfl
          · exact mul_nonneg hW (hμ ω)
      · simp [hd]
    _ ≤ (ε * (∑ x,p x)) * (∑ ω,if data ω = d then μ ω else 0) +
        W * ∑ ω,if data ω = d then μ ω else 0 :=
      add_le_add (fiber_point_potential_bound μ data a Free p hp ε hcap d) le_rfl
    _ = _ := by ring

theorem weighted_fiber_bound (μ w : Ω → ℝ) (data : Ω → D) (C : ℝ)
    (hbound : ∀ d,(∑ ω,if data ω = d then w ω else 0) ≤
      C * ∑ ω,if data ω = d then μ ω else 0) (h : D → ℂ) :
    (∑ ω,w ω * ‖h (data ω)‖^2) ≤ C * ∑ ω,μ ω * ‖h (data ω)‖^2 := by
  rw [sum_by_data w data (fun d => ‖h d‖^2),sum_by_data μ data (fun d => ‖h d‖^2),
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d _
  calc
    _ ≤ ‖h d‖^2 * (C * ∑ ω,if data ω = d then μ ω else 0) :=
      mul_le_mul_of_nonneg_left (hbound d) (sq_nonneg _)
    _ = _ := by ring

theorem lift_apply_norm_sq (μ : Ω → ℝ) (hμ : ∀ ω,0 ≤ μ ω) (h : Ω → ℂ) (ω : Ω) :
    ‖lift μ h ω‖^2 = μ ω * ‖h ω‖^2 := by
  change ‖(Real.sqrt (μ ω) : ℂ) * h ω‖^2 = _
  rw [norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt (hμ ω)]

/-- A conditional potential bound applies to every local coefficient,
including arbitrary complex phases, once it is supported on the tested event. -/
theorem dataSpace_potential_bound (μ : Ω → ℝ) (hμ : ∀ ω,0 ≤ μ ω)
    (data : Ω → D) (p : Ω → ℝ) (E : Ω → Prop) (C : ℝ)
    (hbound : ∀ d,(∑ ω,if data ω = d ∧ E ω then μ ω * p ω else 0) ≤
      C * ∑ ω,if data ω = d then μ ω else 0)
    (f : Hil Ω) (hf : f ∈ dataSpace μ data) (hsupp : ∀ ω,¬ E ω → f ω = 0) :
    (∑ ω,p ω * ‖f ω‖^2) ≤ C * ‖f‖^2 := by
  obtain ⟨h,rfl⟩ := (mem_dataSpace μ data f).mp hf
  have hb : ∀ d,(∑ ω,if data ω = d then (if E ω then μ ω * p ω else 0) else 0) ≤
      C * ∑ ω,if data ω = d then μ ω else 0 := by
    intro d
    convert hbound d using 1
    apply Finset.sum_congr rfl
    intro ω _
    split_ifs <;> simp_all
  have he : (∑ ω,p ω * ‖lift μ (h ∘ data) ω‖^2) =
      ∑ ω,(if E ω then μ ω * p ω else 0) * ‖h (data ω)‖^2 := by
    apply Finset.sum_congr rfl
    intro ω _
    by_cases hE : E ω
    · rw [if_pos hE,lift_apply_norm_sq μ hμ]
      simp only [Function.comp_apply]
      ring
    · rw [if_neg hE,hsupp ω hE]
      simp
  rw [he,lift_norm_sq μ hμ]
  exact weighted_fiber_bound μ (fun ω => if E ω then μ ω * p ω else 0) data C hb h

end WeldedPath.WeightedCoefficients
end

/- Module: WeldedPathEdgeRootDecomposition -/
section

namespace WeldedPath.Supplement.CoefficientDecomposition

open Classical CoefficientOrder EdgeCoefficientSplit FixedDataFunctions
open WeldedPath.WeightedCoefficients WeldedPath.CoefficientStability
open scoped BigOperators

variable {n : ℕ}

/-- Fixed linear maps, independent of the input coefficient, implement the
rooted decomposition. Their ranges are orthogonal even across different
inputs after arbitrary root-data weighting. -/
theorem edge_rooted_linear_decomposition (l : ℕ) (G : WeldedInstance n) (hG : G.IsValid)
    (H : AbsForest n) (hH : H.IsValid) (s : Fin H.k)
    (hconn : ∀ u, H.graph.Reachable s u) (allowed : Fin H.k → Label n → Prop) :
    ∃ D : Fin H.k → Hil (Fin H.k → Label n) →ₗ[ℂ] Hil (Fin H.k → Label n),
      (∀ v f, D v f ∈ localCoefficientSpace H (maskedReference l G H allowed) v) ∧
      (∀ f ∈ ⨆ v, localCoefficientSpace H (maskedReference l G H allowed) v,
        (∑ v, D v f) = f) ∧
      (∀ m : Data H → ℂ, ∀ u v, u ≠ v → ∀ f g,
        inner ℂ (rootMultiplier H s m (D u f)) (rootMultiplier H s m (D v g)) = 0) ∧
      (∀ v f φ, (D v f) φ ≠ 0 →
        v = s ∨ s ∉ H.Ctree φ v) := by
  let μ := maskedReference l G H allowed
  obtain ⟨order, hord, hroot⟩ := exists_root_order H s hconn
  let A : ℕ → Submodule ℂ (Hil (Fin H.k → Label n)) :=
    fun i => if hi : i < H.k then localCoefficientSpace H μ (order ⟨i, hi⟩) else ⊥
  have hA (i : Fin H.k) : A i.val = localCoefficientSpace H μ (order i) := by
    simp only [A, dif_pos i.isLt]
  let Q : ℕ → Submodule ℂ (Hil (Fin H.k → Label n)) := fun i =>
    if hi : i < H.k then eventSpace (fun φ =>
      order ⟨i, hi⟩ = s ∨ s ∉ H.Ctree φ (order ⟨i, hi⟩)) else ⊥
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
          change rv ∈ eventSpace (fun φ => order ii = s ∨ s ∉ H.Ctree φ (order ii))
          intro φ hφ
          by_cases hw : H.IsWeldUnder φ e
          · have hsct : s ∈ H.Ctree φ (order ii) := by tauto
            exact (hsout (FixedDataSeparator.ctree_on_side H φ e P hcut hw
              (order ii) hc s hsct)).elim
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
    change D i f ∈ eventSpace (fun ψ => order i = s ∨ s ∉ H.Ctree ψ (order i)) at hq
    have hp : order i = s ∨ s ∉ H.Ctree φ (order i) := by
      by_contra hn
      exact hne (hq φ hn)
    simpa only [i, Equiv.apply_symm_apply] using hp

end WeldedPath.Supplement.CoefficientDecomposition
end

/- Module: WeldedPathEdgeAnchoredSplit -/
section

namespace WeldedPath.Supplement.EdgeAnchoredSplit

open Classical BoundarySector FixedCollisions FixedData CoefficientDecomposition FixedDataFunctions
open WeldedPath.WeightedCoefficients WeldedPath.HilbertSupport
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}

def fixedStatus (H : AbsForest n) (s a : Fin H.k) (b : Bool)
    (φ : Fin H.k → Label n) : Prop := (s ∈ H.Ctree φ a) ↔ b = true

theorem fixedStatus_factors (H : AbsForest n) (hH : H.IsValid)
    (s a : Fin H.k) (b : Bool) :
    Function.FactorsThrough (fixedStatus H s a b) (fun φ => H.Wfix φ a) := by
  intro φ ψ h
  unfold fixedStatus
  have hc : H.Ctree φ a = H.Ctree ψ a := congrArg Prod.fst h
  rw [hc]

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
  by_cases h : s ∈ H.Ctree φ a <;> simp [fixedStatus, h]

theorem splitMap_support (H : AbsForest n) (B : Finset ℕ)
    (F : Finset (Fin H.k)) (s a : Fin H.k) (b : Bool)
    (f : Hil (Fin H.k → Label n)) (φ : Fin H.k → Label n)
    (hf : splitMap (l := l) (G := G) H B F s a b f φ ≠ 0) :
    b = true ↔ s ∈ H.Ctree φ a := by
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
    by_cases h : s ∈ H.Ctree φ a <;>
      simp [rootMultiplier, splitMap_apply, fixedStatus, h]


end WeldedPath.Supplement.EdgeAnchoredSplit
end

/- Module: WeldedPathEdgeSectorDecomposition -/
section

namespace WeldedPath.Supplement.AllSectorLinear

open Classical BoundarySector AllBoundaryStability EdgeAnchoredSplit
open CoefficientDecomposition FixedDataFunctions EdgeCoefficientSplit
open WeldedPath.WeightedCoefficients WeldedPath.HilbertSupport WeldedPath.SectorLinearAssembly
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}

def treeFixed (H : AbsForest n) (s : Fin H.k) (i : Index H) : Prop :=
  if i.1 = ∅ then i.2.1 = s else i.2.2 = true

/-- One fixed linear decomposition covers all exact boundary patterns.
Each summand has an index-fixed free/fixed status for the tested root. -/
theorem edge_rooted_all_sector_linear (l : ℕ) (G : WeldedInstance n) (hG : G.IsValid)
    (H : AbsForest n) (hH : H.IsValid) (B : Finset ℕ) (s : Fin H.k)
    (hs : ∀ u, H.graph.Reachable s u) :
    ∃ D : Index H → Hil (Fin H.k → Label n) →ₗ[ℂ] Hil (Fin H.k → Label n),
      (∀ i f, D i f ∈ dataSpace (weight l G H B s i) (fun φ => H.Wfix φ (vertex H s i))) ∧
      (∀ f ∈ allSectorSpace l G H B, (∑ i, D i f) = f) ∧
      (∀ m : Data H → ℂ, ∀ i j, i ≠ j → ∀ f g,
        inner ℂ (rootMultiplier H s m (D i f)) (rootMultiplier H s m (D j g)) = 0) ∧
      (∀ i f φ, D i f φ ≠ 0 → (treeFixed H s i ↔ s ∈ H.Ctree φ (vertex H s i))) := by
  obtain ⟨E, hE, hsumE, horthE, hsupportE⟩ := edge_rooted_linear_decomposition
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
    · simp only [treeFixed, vertex, hF, if_true]
      have hb : b ≠ true := by
        intro hb
        simp [L, hF, hb] at hne
      have hEne : E v ((eventSpace (boundaryPattern H B F)).starProjection f) φ ≠ 0 := by
        simpa only [L, hF, if_true, hb, Bool.false_eq_true, if_false] using hne
      constructor
      · rintro rfl
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,SimpleGraph.Reachable.refl _⟩
      · intro hfix
        rcases hsupportE v _ φ hEne with h | h
        · exact h
        · exact (h hfix).elim
    · have hv : v = anchor H s F := by
        by_contra hv
        simp [L, hF, hv] at hne
      simp only [treeFixed, vertex, hF, if_false]
      apply splitMap_support H B F s (anchor H s F) b _ φ
      simpa only [L, hF, if_false, hv, if_true] using hne

end WeldedPath.Supplement.AllSectorLinear
end

/- Module: WeldedPathEdgeLocalPotential -/
section

namespace WeldedPath.Supplement.EdgePotential

open Classical KappaKernel SourceFiberBound ConnectedConcentration FixedDataFunctions
open WeldedPath.WeightedCoefficients
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}

noncomputable def potentialBudget (n : ℕ) (B : Finset ℕ) (k : ℕ) : ℝ :=
  (8 / (2 : ℝ)^n) * ((B.card : ℝ) + 12 * (k : ℝ) * ((n : ℝ)+1)) +
    4 * ((B.card : ℝ)+(k : ℝ)) / (2 : ℝ)^n


theorem weld_of_mem_sfix_not_ctree (H : AbsForest n) (φ : Fin H.k → Label n)
    (s a : Fin H.k) (hf : a ∈ H.Sfix φ s) (ht : a ∉ H.Ctree φ s) :
    (φ a).val ∈ Vweld n := by
  rcases Finset.mem_union.mp hf with hf | hf
  · exact (ht hf).elim
  · obtain ⟨p,hp,hw,he⟩ := (Finset.mem_filter.mp hf).2
    rcases he with ⟨_,he⟩ | ⟨_,he⟩
    · simpa only [he] using hw.2
    · simpa only [he] using hw.1

/-- The concrete conditional estimate behind Eq. 70.  The tested vertex
is either free with point mass at most 8/N, or fixed immediately across a weld. -/
theorem local_potential_bound (H : AbsForest n) (hH : H.IsValid)
    (μ : (Fin H.k → Label n) → ℝ) (hμ : ∀ φ,0 ≤ μ φ)
    (s : Fin H.k) (hs : ∀ u,H.graph.Reachable s u)
    (hG : G.IsValid) (hn : 16 ≤ n) (hl : 2 ≤ l) (hln : l ≤ n-4)
    (B : Finset ℕ) (hB : Vbd n l ⊆ B) (hBw : Disjoint B (Vweld n))
    (hsmall : (H.k : ℝ)*(B.card : ℝ)*(4/(2:ℝ)^n) ≤ 1/2)
    (hsource : ∀ φ₀,0 < μ φ₀ → H.muRef l G φ₀ ≠ 0 ∧ ∀ φ,
      (if H.Wfix φ s = H.Wfix φ₀ s then μ φ else 0) = sourceWeight l G H φ₀ s B φ)
    (a : Fin H.k) (α : Fin 3) (k : ℕ)
    (f : Hil (Fin H.k → Label n)) (hf : f ∈ dataSpace μ (fun φ => H.Wfix φ s))
    (hsupp : ∀ φ,a ∈ H.Ctree φ s → f φ = 0) :
    (∑ φ,potential l G α B k (φ a) * ‖f φ‖^2) ≤ potentialBudget n B k * ‖f‖^2 := by
  apply dataSpace_potential_bound μ hμ (fun φ => H.Wfix φ s)
    (fun φ => potential l G α B k (φ a)) (fun φ => a ∉ H.Ctree φ s)
    (potentialBudget n B k) ?_ f hf (fun φ hφ => hsupp φ (not_not.mp hφ))
  intro d
  have hc := fiber_potential_bound_with_fixed μ hμ (fun φ => H.Wfix φ s) (fun φ => φ a)
    (fun φ => a ∉ H.Sfix φ s) (fun φ => a ∉ H.Ctree φ s)
    (potential l G α B k) (potential_nonneg α B k) (8/(2:ℝ)^n)
    (4*((B.card:ℝ)+(k:ℝ))/(2:ℝ)^n) (by positivity)
    (fun d x => by
      have hh := free_point_fiber_bound H hH μ hμ s hs hG hn hl hln B hB hBw hsmall
        hsource a x d
      convert hh using 1 <;> congr 1
      all_goals first
        | rfl
        | (apply Finset.sum_congr rfl; intro φ _; split_ifs <;> rfl)
        | (funext φ; split_ifs <;> rfl))
    (fun φ ht hf => potential_weld_le hG (by omega) (by omega) α B k (φ a)
      (weld_of_mem_sfix_not_ctree H φ s a (not_not.mp hf) ht)) d
  refine hc.trans (mul_le_mul_of_nonneg_right ?_ ?_)
  · unfold potentialBudget
    exact add_le_add (mul_le_mul_of_nonneg_left
      (potential_sum_le hG (by omega) α B k) (by positivity : (0 : ℝ) ≤ 8/(2:ℝ)^n)) le_rfl
  · exact Finset.sum_nonneg fun φ _ => by split_ifs; exact hμ φ; rfl

end WeldedPath.Supplement.EdgePotential
end

/- Module: WeldedPathEdgeWeightedPotential -/
section

namespace WeldedPath.Supplement.EdgePotential

open Classical AllSectorLinear CoefficientDecomposition FixedDataFunctions EdgeCoefficientSplit
open WeldedPath.WeightedCoefficients WeldedPath.CoefficientStability
open WeldedPath.ProductDecomposition
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}

noncomputable def rootPotentialMultiplier (H : AbsForest n) (a : Fin H.k)
    (p : Label n → ℝ) : Hil (Fin H.k → Label n) →ₗ[ℂ] Hil (Fin H.k → Label n) :=
  rootMultiplier H a (fun d => (Real.sqrt (p (fixedRootValue H a a d)) : ℂ))

theorem rootPotentialMultiplier_norm_sq (H : AbsForest n) (hH : H.IsValid)
    (a : Fin H.k) (p : Label n → ℝ) (hp : ∀ x,0 ≤ p x) (f : Hil (Fin H.k → Label n)) :
    ‖rootPotentialMultiplier H a p f‖^2 = ∑ φ,p (φ a) * ‖f φ‖^2 := by
  rw [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro φ _
  change ‖(Real.sqrt (p (fixedRootValue H a a (H.Wfix φ a))) : ℂ) * f φ‖^2 = _
  rw [fixedRootValue_eq H hH a a φ (root_mem_sfix H φ a),norm_mul,mul_pow,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt (hp _)]

noncomputable def gPart (H : AbsForest n) (a : Fin H.k)
    (D : Index H → Hil (Fin H.k → Label n) →ₗ[ℂ] Hil (Fin H.k → Label n))
    (f : Hil (Fin H.k → Label n)) : Hil (Fin H.k → Label n) :=
  ∑ i,if treeFixed H a i then 0 else D i f

noncomputable def gOperator (H : AbsForest n) (a : Fin H.k)
    (D : Index H → Hil (Fin H.k → Label n) →ₗ[ℂ] Hil (Fin H.k → Label n)) :
    Hil (Fin H.k → Label n) →ₗ[ℂ] Hil (Fin H.k → Label n) :=
  ∑ i,if treeFixed H a i then 0 else D i

theorem gOperator_apply (H : AbsForest n) (a : Fin H.k)
    (D : Index H → Hil (Fin H.k → Label n) →ₗ[ℂ] Hil (Fin H.k → Label n))
    (f : Hil (Fin H.k → Label n)) : gOperator H a D f = gPart H a D f := by
  simp only [gOperator,gPart,LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> rfl

theorem gPart_norm_le (H : AbsForest n) (a : Fin H.k)
    (D : Index H → Hil (Fin H.k → Label n) →ₗ[ℂ] Hil (Fin H.k → Label n))
    (f : Hil (Fin H.k → Label n)) (hsum : (∑ i,D i f) = f)
    (horth : ∀ i j,i ≠ j → inner ℂ (D i f) (D j f) = 0) :
    ‖gPart H a D f‖^2 ≤ ‖f‖^2 := by
  have ho : ∀ i j,i ≠ j → inner ℂ
      (if treeFixed H a i then 0 else D i f) (if treeFixed H a j then 0 else D j f) = 0 := by
    intro i j hij
    split_ifs <;> first
      | exact horth i j hij
      | simp only [inner_zero_left,inner_zero_right]
  have hnorm : ‖f‖^2 = ∑ i,‖D i f‖^2 := by
    calc
      _ = ‖∑ i,D i f‖^2 := congrArg (fun z => ‖z‖^2) hsum.symm
      _ = _ := norm_sum_sq_orthogonal _ horth
  rw [gPart,norm_sum_sq_orthogonal _ ho,hnorm]
  apply Finset.sum_le_sum
  intro i _
  split_ifs
  · simp only [norm_zero,zero_pow (by decide : 2 ≠ 0)]
    exact sq_nonneg _
  · exact le_rfl


/-- Eq. 70 for the actual all-boundary coefficient decomposition.  Root-data
weighted orthogonality eliminates any factor equal to the number of sectors. -/
theorem g_potential_bound (H : AbsForest n) (hH : H.IsValid)
    (a : Fin H.k) (ha : ∀ u,H.graph.Reachable a u)
    (hG : G.IsValid) (hn : 16 ≤ n) (hl : 2 ≤ l) (hln : l ≤ n-4)
    (B : Finset ℕ) (hB : Vbd n l ⊆ B) (hBw : Disjoint B (Vweld n))
    (hsmall : (H.k : ℝ)*(B.card : ℝ)*(4/(2:ℝ)^n) ≤ 1/2)
    (D : Index H → Hil (Fin H.k → Label n) →ₗ[ℂ] Hil (Fin H.k → Label n))
    (hD : ∀ i f,D i f ∈ dataSpace (weight l G H B a i) (fun φ => H.Wfix φ (vertex H a i)))
    (horth : ∀ m : Data H → ℂ,∀ i j,i ≠ j → ∀ f g,
      inner ℂ (rootMultiplier H a m (D i f)) (rootMultiplier H a m (D j g)) = 0)
    (hsupport : ∀ i f φ,D i f φ ≠ 0 → (treeFixed H a i ↔ a ∈ H.Ctree φ (vertex H a i)))
    (α : Fin 3) (k : ℕ) (f : Hil (Fin H.k → Label n)) :
    (∑ φ,potential l G α B k (φ a) * ‖gPart H a D f φ‖^2) ≤
      potentialBudget n B k * ‖gPart H a D f‖^2 := by
  let v : Index H → Hil (Fin H.k → Label n) := fun i => if treeFixed H a i then 0 else D i f
  have hvorth : ∀ m : Data H → ℂ,∀ i j,i ≠ j →
      inner ℂ (rootMultiplier H a m (v i)) (rootMultiplier H a m (v j)) = 0 := by
    intro m i j hij
    dsimp only [v]
    split_ifs <;> first
      | exact horth m i j hij f f
      | simp only [map_zero,inner_zero_left,inner_zero_right]
  have hverr (i : Index H) :
      ‖rootPotentialMultiplier H a (potential l G α B k) (v i)‖^2 ≤
        potentialBudget n B k * ‖v i‖^2 := by
    by_cases hi : treeFixed H a i
    · simp only [v,if_pos hi,map_zero,norm_zero,zero_pow (by decide : 2 ≠ 0),mul_zero,le_refl]
    · simp only [v,if_neg hi]
      rw [rootPotentialMultiplier_norm_sq H hH a _ (potential_nonneg α B k)]
      apply local_potential_bound H hH (weight l G H B a i) (weight_nonneg H hH B a i)
        (vertex H a i) (fun u => (ha (vertex H a i)).symm.trans (ha u))
        hG hn hl hln B hB hBw hsmall (ConnectedResolution.weight_source H hH B a ha i)
        a α k (D i f) (hD i f)
      intro φ hct
      by_contra hne
      exact hi ((hsupport i f φ hne).mpr hct)
  rw [← rootPotentialMultiplier_norm_sq H hH a _ (potential_nonneg α B k)]
  change ‖rootPotentialMultiplier H a (potential l G α B k) (∑ i,v i)‖^2 ≤ _
  have hpo : ∀ i j,i ≠ j → inner ℂ
      (rootPotentialMultiplier H a (potential l G α B k) (v i))
      (rootPotentialMultiplier H a (potential l G α B k) (v j)) = 0 := by
    intro i j hij
    exact hvorth _ i j hij
  rw [map_sum,norm_sum_sq_orthogonal _ hpo]
  calc
    _ ≤ ∑ i,potentialBudget n B k * ‖v i‖^2 := Finset.sum_le_sum fun i _ => hverr i
    _ = potentialBudget n B k * ∑ i,‖v i‖^2 := (Finset.mul_sum _ _ _).symm
    _ = _ := by
      rw [← norm_sum_sq_orthogonal v (fun i j hij => by
        simpa only [rootMultiplier_one] using hvorth (fun _ => 1) i j hij)]
      rfl

theorem edge_potential_resolution (H : AbsForest n) (hH : H.IsValid)
    (a : Fin H.k) (ha : ∀ u,H.graph.Reachable a u)
    (hG : G.IsValid) (hn : 16 ≤ n) (hl : 2 ≤ l) (hln : l ≤ n-4)
    (B : Finset ℕ) (hB : Vbd n l ⊆ B) (hBw : Disjoint B (Vweld n))
    (hsmall : (H.k : ℝ)*(B.card : ℝ)*(4/(2:ℝ)^n) ≤ 1/2) :
    ∃ D : Index H → Hil (Fin H.k → Label n) →ₗ[ℂ] Hil (Fin H.k → Label n),
      (∀ i f,D i f ∈ dataSpace (weight l G H B a i) (fun φ => H.Wfix φ (vertex H a i))) ∧
      (∀ f ∈ AllBoundaryStability.allSectorSpace l G H B,(∑ i,D i f) = f) ∧
      (∀ m : Data H → ℂ,∀ i j,i ≠ j → ∀ f g,
        inner ℂ (rootMultiplier H a m (D i f)) (rootMultiplier H a m (D j g)) = 0) ∧
      (∀ i f φ,D i f φ ≠ 0 → (treeFixed H a i ↔ a ∈ H.Ctree φ (vertex H a i))) ∧
      (∀ f ∈ AllBoundaryStability.allSectorSpace l G H B,‖gPart H a D f‖^2 ≤ ‖f‖^2) ∧
      (∀ α k f,(∑ φ,potential l G α B k (φ a) * ‖gPart H a D f φ‖^2) ≤
        potentialBudget n B k * ‖gPart H a D f‖^2) := by
  obtain ⟨D,hD,hsum,horth,hsupport⟩ := edge_rooted_all_sector_linear l G hG H hH B a ha
  refine ⟨D,hD,hsum,horth,hsupport,?_,?_⟩
  · intro f hf
    exact gPart_norm_le H a D f (hsum f hf) (fun i j hij => by
      simpa only [rootMultiplier_one] using horth (fun _ => 1) i j hij f f)
  · intro α k f
    exact g_potential_bound H hH a ha hG hn hl hln B hB hBw hsmall D hD horth hsupport α k f

end WeldedPath.Supplement.EdgePotential
end

end

section

/- Module: WeldedPathRawReference -/
section

namespace WeldedPath.Supplement.EdgeBookkeeping

open Classical ForestFactorization DatabaseSupport KappaKernel KappaWalk
open FiniteWeightedForest
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}













end WeldedPath.Supplement.EdgeBookkeeping
end

/- Module: GraphBridgeReachability -/
section

namespace WeldedPath.GraphBridge

variable {V : Type*}



end WeldedPath.GraphBridge
end

/- Module: WeldedPathEdgeJoin -/
section

namespace WeldedPath.Supplement.EdgeBookkeeping

open Classical AssignmentDatabase

variable {n l : ℕ} {G : WeldedInstance n}








end WeldedPath.Supplement.EdgeBookkeeping
end

/- Module: WeldedPathJoinDatabase -/
section

namespace WeldedPath.Supplement.EdgeBookkeeping

open Classical AssignmentDatabase
open WeldedPath.CompressedPrimitive InjDb

variable {n l : ℕ} {G : WeldedInstance n}


end WeldedPath.Supplement.EdgeBookkeeping
end

/- Module: WeldedPathJoinWeight -/
section

namespace WeldedPath.Supplement.EdgeBookkeeping

open Classical ForestFactorization FiniteWeightedForest
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}





end WeldedPath.Supplement.EdgeBookkeeping
end

/- Module: WeldedPathJoinFixedData -/
section

namespace WeldedPath.Supplement.EdgeBookkeeping

open Classical DatabaseSupport

variable {n : ℕ}





end WeldedPath.Supplement.EdgeBookkeeping
end

/- Module: WeldedPathLeafGood -/
section

namespace WeldedPath.Supplement.EdgeBookkeeping

open Classical

variable {n l : ℕ} {G : WeldedInstance n}



end WeldedPath.Supplement.EdgeBookkeeping
end

/- Module: WeldedPathJoinDescription -/
section

namespace WeldedPath.Supplement.EdgeBookkeeping

open Classical DatabaseSupport

variable {n l : ℕ} {G : WeldedInstance n}




end WeldedPath.Supplement.EdgeBookkeeping
end

/- Module: WeldedPathLeafGoodVector -/
section

namespace WeldedPath.Supplement.EdgeBookkeeping

open Classical DatabaseSupport ForestFactorization KappaKernel
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}







end WeldedPath.Supplement.EdgeBookkeeping
end

/- Module: WeldedPathJoinOtherComponent -/
section

namespace WeldedPath.Supplement.EdgeBookkeeping

open Classical DatabaseSupport

variable {n : ℕ}





end WeldedPath.Supplement.EdgeBookkeeping
end

/- Module: WeldedPathJoinBoundary -/
section

namespace WeldedPath.Supplement.EdgeBookkeeping

open Classical DatabaseSupport

variable {n : ℕ}




end WeldedPath.Supplement.EdgeBookkeeping
end

/- Module: WeldedPathJoinGood -/
section

namespace WeldedPath.Supplement.EdgeBookkeeping

open Classical

variable {n l : ℕ} {G : WeldedInstance n}





end WeldedPath.Supplement.EdgeBookkeeping
end

/- Module: WeldedPathEdgeKernelBound -/
section

namespace WeldedPath.Supplement.EdgePotential

open Classical KappaKernel SourceFiberBound ConnectedConcentration FixedDataFunctions
open AllSectorLinear CoefficientDecomposition EdgeCoefficientSplit
open WeldedPath.WeightedCoefficients WeldedPath.CoefficientStability WeldedPath.ProductDecomposition
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}





end WeldedPath.Supplement.EdgePotential
end

/- Module: WeldedPathEdgeGoodVectors -/
section

namespace WeldedPath.Supplement.EdgeBookkeeping

open Classical DatabaseSupport ForestFactorization KappaKernel
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}








end WeldedPath.Supplement.EdgeBookkeeping
end

end

section

namespace WeldedPath.Supplement.LabelBookkeeping

open Classical DatabaseSupport

variable {n : ℕ}














end WeldedPath.Supplement.LabelBookkeeping

end

section

namespace WeldedPath.Supplement.EdgeBookkeeping

open Classical LabelBookkeeping DatabaseSupport

variable {n : ℕ}












end WeldedPath.Supplement.EdgeBookkeeping

end

section

namespace WeldedPath.Supplement.ReferenceSizes

open Classical LoopProof




end WeldedPath.Supplement.ReferenceSizes

end

section

namespace WeldedPath.Supplement.EdgeBookkeeping

open Classical EdgePotential WeldedPath.WeightedCoefficients
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}




end WeldedPath.Supplement.EdgeBookkeeping

end

section

namespace WeldedPath.Supplement.DatabaseSupport

open Classical WeightedCoefficients HilbertSupport

variable {n l : ℕ} {G : WeldedInstance n}






end WeldedPath.Supplement.DatabaseSupport

end

section

namespace WeldedPath.Supplement.DatabaseSupport

open Classical

variable {n l : ℕ} {G : WeldedInstance n}





end WeldedPath.Supplement.DatabaseSupport

end

section

namespace WeldedPath.Supplement.DatabaseSupport

open Classical

variable {n l : ℕ} {G : WeldedInstance n}













end WeldedPath.Supplement.DatabaseSupport

end

section

namespace WeldedPath.CoefficientTransport

open Classical WeightedCoefficients HilbertSupport

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]







end WeldedPath.CoefficientTransport

end

section

namespace WeldedPath.Supplement.DatabaseSupport

open Classical
open WeldedPath.CoefficientTransport WeldedPath.WeightedCoefficients

variable {n : ℕ}










end WeldedPath.Supplement.DatabaseSupport

end

section

namespace WeldedPath.Supplement.DatabaseSupport

open Classical ForestFactorization

variable {n l : ℕ} {G : WeldedInstance n}





end WeldedPath.Supplement.DatabaseSupport

end

section

namespace WeldedPath.CoefficientStability

open scoped BigOperators

variable {E β ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [Fintype β] [Fintype ι]


end WeldedPath.CoefficientStability

end

section

namespace WeldedPath.ProductDecomposition

open Classical HilbertSupport WeightedCoefficients CoefficientStability CollisionStability
open scoped BigOperators

variable {X Y A β ι : Type*} [Fintype X] [Fintype Y] [Fintype β] [Fintype ι]
  [DecidableEq X] [DecidableEq Y] [DecidableEq A]


end WeldedPath.ProductDecomposition

end

section

namespace WeldedPath.Supplement.ConnectedResolution

open Classical AllSectorLinear AllBoundaryStability BoundarySector FixedCollisions
open FixedDataFunctions
open WeldedPath.WeightedCoefficients WeldedPath.ProductDecomposition
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n} {Y : Type*} [Fintype Y] [DecidableEq Y]


end WeldedPath.Supplement.ConnectedResolution

end

section

namespace WeldedPath.ProductDecomposition

open Classical HilbertSupport WeightedCoefficients CoefficientStability
open scoped BigOperators

variable {X Y W A B Z ι κ : Type*} [Fintype X] [Fintype Y] [Fintype W]
  [Fintype ι] [Fintype κ] [DecidableEq X] [DecidableEq Y] [DecidableEq W]
  [DecidableEq A] [DecidableEq B]


end WeldedPath.ProductDecomposition

end

section

namespace WeldedPath.Supplement.ConnectedResolution

open Classical AllBoundaryStability
open WeldedPath.WeightedCoefficients WeldedPath.ProductDecomposition

variable {n l : ℕ} {G : WeldedInstance n} {W : Type*} [Fintype W] [DecidableEq W]


end WeldedPath.Supplement.ConnectedResolution

end

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




end WeldedPath.Supplement.DisconnectedStability

end

section

namespace WeldedPath.Supplement.DisconnectedStability

open Classical FixedCollisions
open WeldedPath.WeightedCoefficients WeldedPath.CoefficientStability
open scoped BigOperators

variable {n : ℕ}


end WeldedPath.Supplement.DisconnectedStability

end

section

namespace WeldedPath.Supplement.DisconnectedStability

open Classical
open WeldedPath.WeightedCoefficients

variable {n l : ℕ} {G : WeldedInstance n}


end WeldedPath.Supplement.DisconnectedStability

end

section

namespace WeldedPath.Supplement.DatabaseSupport

open Classical DescriptionCoefficients ForestFactorization DisconnectedStability
open WeldedPath.WeightedCoefficients

variable {n l : ℕ} {G : WeldedInstance n}







end WeldedPath.Supplement.DatabaseSupport

end

section

namespace WeldedPath.Supplement.DatabaseSupport

open Classical DescriptionCoefficients DisconnectedStability WeightedCoefficients

variable {n l : ℕ} {G : WeldedInstance n}











end WeldedPath.Supplement.DatabaseSupport

end

section

namespace WeldedPath.Supplement.DatabaseSupport

open Classical

variable {n l : ℕ} {G : WeldedInstance n}


end WeldedPath.Supplement.DatabaseSupport

end

section

namespace WeldedPath.Supplement.DatabaseSupport

open Classical DescriptionCoefficients DisconnectedStability
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}









end WeldedPath.Supplement.DatabaseSupport

end

section

namespace WeldedPath.Supplement.DatabaseSupport

open Classical
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}


end WeldedPath.Supplement.DatabaseSupport

namespace WeldedPath.Supplement.EdgeBookkeeping

open Classical DatabaseSupport EdgePotential KappaKernel
open WeldedPath.WeightedCoefficients
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}




end WeldedPath.Supplement.EdgeBookkeeping

end

section

namespace WeldedPath.CompressedPrimitive

open Classical InjDb Supplement HilbertSupport RegisterTransport EncodedOracleUnitary
open scoped BigOperators
















end WeldedPath.CompressedPrimitive

end

section

/- Module: RecoverableFiberBound -/
section

namespace WeldedPath.UniformFiberEncoding

open Classical

variable {A B C Z : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype Z]



end WeldedPath.UniformFiberEncoding
end

/- Module: WeldedPathEdgeGlobalPotential -/
section

namespace WeldedPath.Supplement.EdgePotential

open Classical ComponentForest DisconnectedStability AllSectorLinear CoefficientDecomposition
open WeldedPath.ProductDecomposition WeldedPath.WeightedCoefficients
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}

noncomputable def componentOperator (H : AbsForest n) (r : Roots H)
    (T : Hil (LocalAssignment H r) →ₗ[ℂ] Hil (LocalAssignment H r)) :
    Hil (Fin H.k → Label n) →ₗ[ℂ] Hil (Fin H.k → Label n) :=
  (regroupOneHil H r).symm.toLinearMap.comp
    ((linearTensor T (LinearMap.id : Hil (OneSpectator H r) →ₗ[ℂ] Hil (OneSpectator H r))).comp
      (regroupOneHil H r).toLinearMap)






end WeldedPath.Supplement.EdgePotential
end

/- Module: WeldedPathEdgeEraseDatabase -/
section

namespace WeldedPath.Supplement.EdgeBookkeeping

open Classical AssignmentDatabase DatabaseSupport KappaKernel
open CompressedPrimitive InjDb

variable {n l : ℕ} {G : WeldedInstance n}











end WeldedPath.Supplement.EdgeBookkeeping
end

end

section

namespace WeldedPath.Supplement.EdgeBookkeeping

open Classical AssignmentDatabase DatabaseSupport DatabaseReadout KappaKernel
open CompressedPrimitive InjDb

variable {n l : ℕ} {G : WeldedInstance n}











end WeldedPath.Supplement.EdgeBookkeeping

end

section

namespace WeldedPath.Supplement.EdgeSourceSpan

open Classical DescriptionCoefficients ConnectedConcentration BoundaryCoefficients FixedData
open AllSectorLinear
open WeldedPath.WeightedCoefficients
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}

theorem sourceAmplitude_reroot (H : AbsForest n) (hH : H.IsValid)
    (B : Finset ℕ) (a v : Fin H.k) (hconn : ∀ u w, H.graph.Reachable u w)
    (φ₀ : Fin H.k → Label n) (ha : a ∈ H.Ctree φ₀ v) :
    sourceAmplitude l G H B v φ₀ = sourceAmplitude l G H B a φ₀ := by
  have hC₀ := ctree_eq_of_mem H φ₀ a v ha
  have hS₀ : H.Sfix φ₀ v = H.Sfix φ₀ a := by simp only [AbsForest.Sfix, hC₀]
  ext φ
  change (Real.sqrt (sourceWeight l G H φ₀ v B φ) : ℂ) =
    (Real.sqrt (sourceWeight l G H φ₀ a B φ) : ℂ)
  have hw : H.Wfix φ v = H.Wfix φ₀ v ↔ H.Wfix φ a = H.Wfix φ₀ a := by
    rw [wfix_eq_iff_agree_sfix H hH, wfix_eq_iff_agree_sfix H hH, hS₀]
  by_cases hv : H.Wfix φ v = H.Wfix φ₀ v
  · have hC' : H.Ctree φ v = H.Ctree φ₀ v := congrArg Prod.fst hv
    have ha' : a ∈ H.Ctree φ v := hC'.symm ▸ ha
    have hC := ctree_eq_of_mem H φ a v ha'
    simp only [sourceWeight, hv, hw.mp hv, true_and, hC]
    congr 3
    exact propext ⟨fun h u _ hu => h u (hconn v u) hu,
      fun h u _ hu => h u (hconn a u) hu⟩
  · simp only [sourceWeight, hv, mt hw.mpr hv, false_and, if_false]

theorem supported_dataSpace_source_span (H : AbsForest n) (hH : H.IsValid)
    (B : Finset ℕ) (a : Fin H.k) (ha : ∀ u, H.graph.Reachable a u)
    (i : Index H) (P : (Fin H.k → Label n) → Prop)
    (f : Hil (Fin H.k → Label n))
    (hf : f ∈ dataSpace (weight l G H B a i) (fun φ => H.Wfix φ (vertex H a i)))
    (hsupp : ∀ φ, f φ ≠ 0 → P φ) :
    f ∈ Submodule.span ℂ {g | ∃ φ₀, P φ₀ ∧
      g = sourceAmplitude l G H B (vertex H a i) φ₀} := by
  let μ := weight l G H B a i
  let data := fun φ => H.Wfix φ (vertex H a i)
  let S := Submodule.span ℂ {g | ∃ φ₀, P φ₀ ∧
    g = sourceAmplitude l G H B (vertex H a i) φ₀}
  obtain ⟨h, heq⟩ := (mem_dataSpace μ data f).mp hf
  have hval (φ) : f φ = (Real.sqrt (μ φ) : ℂ) * h (data φ) := by
    rw [← heq]; rfl
  rw [← heq, lift_eq_sum_fibers]
  apply S.sum_mem
  intro d _
  by_cases hex : ∃ φ₀, data φ₀ = d ∧ f φ₀ ≠ 0
  · obtain ⟨φ₀, hd, hne⟩ := hex
    have hμ : 0 < μ φ₀ := by
      apply lt_of_le_of_ne (weight_nonneg H hH B a i φ₀)
      intro hz
      change 0 = μ φ₀ at hz
      apply hne
      rw [hval, ← hz, Real.sqrt_zero, Complex.ofReal_zero, zero_mul]
    have hsource := (ConnectedResolution.weight_source H hH B a ha i φ₀ hμ).2
    have he : fiberAmplitude μ data d = sourceAmplitude l G H B (vertex H a i) φ₀ := by
      ext φ
      change (Real.sqrt (μ φ) : ℂ) * (if data φ = d then 1 else 0) =
        (Real.sqrt (sourceWeight l G H φ₀ (vertex H a i) B φ) : ℂ)
      rw [← hsource φ]
      change (Real.sqrt (μ φ) : ℂ) * (if data φ = d then 1 else 0) =
        (Real.sqrt (if data φ = data φ₀ then μ φ else 0) : ℂ)
      rw [hd]
      split_ifs <;> simp
    rw [he]
    exact S.smul_mem _ (Submodule.subset_span ⟨φ₀, hsupp φ₀ hne, rfl⟩)
  · have hz : h d • fiberAmplitude μ data d = 0 := by
      ext φ
      change h d * ((Real.sqrt (μ φ) : ℂ) * (if data φ = d then 1 else 0)) = 0
      by_cases hd : data φ = d
      · have hfzero : f φ = 0 := Classical.byContradiction (fun hn => hex ⟨φ,hd,hn⟩)
        rw [if_pos hd, mul_one, mul_comm, ← hd, ← hval, hfzero]
      · rw [if_neg hd, mul_zero, mul_zero]
    rw [hz]
    exact S.zero_mem

theorem fixed_piece_source_span (H : AbsForest n) (hH : H.IsValid)
    (B : Finset ℕ) (a : Fin H.k) (ha : ∀ u, H.graph.Reachable a u)
    (i : Index H) (f : Hil (Fin H.k → Label n))
    (hf : f ∈ dataSpace (weight l G H B a i) (fun φ => H.Wfix φ (vertex H a i)))
    (hsupp : ∀ φ, f φ ≠ 0 → a ∈ H.Ctree φ (vertex H a i)) :
    f ∈ Submodule.span ℂ {g | ∃ φ₀, g = sourceAmplitude l G H B a φ₀} := by
  apply (Submodule.span_le.mpr ?_) (supported_dataSpace_source_span H hH B a ha i _ f hf hsupp)
  rintro g ⟨φ₀, hφ₀, rfl⟩
  rw [sourceAmplitude_reroot H hH B a (vertex H a i)
    (fun u w => (ha u).symm.trans (ha w)) φ₀ hφ₀]
  exact Submodule.subset_span ⟨φ₀, rfl⟩

theorem fixed_sum_source_span (H : AbsForest n) (hH : H.IsValid)
    (B : Finset ℕ) (a : Fin H.k) (ha : ∀ u, H.graph.Reachable a u)
    (D : Index H → Hil (Fin H.k → Label n) →ₗ[ℂ] Hil (Fin H.k → Label n))
    (hD : ∀ i f, D i f ∈ dataSpace (weight l G H B a i) (fun φ => H.Wfix φ (vertex H a i)))
    (hsupp : ∀ i f φ, D i f φ ≠ 0 → (treeFixed H a i ↔ a ∈ H.Ctree φ (vertex H a i)))
    (f : Hil (Fin H.k → Label n)) :
    (∑ i, if treeFixed H a i then D i f else 0) ∈
      Submodule.span ℂ {g | ∃ φ₀, g = sourceAmplitude l G H B a φ₀} := by
  apply Submodule.sum_mem
  intro i _
  split_ifs with hi
  · exact fixed_piece_source_span H hH B a ha i (D i f) (hD i f)
      (fun φ hφ => (hsupp i f φ hφ).mp hi)
  · exact Submodule.zero_mem _

end WeldedPath.Supplement.EdgeSourceSpan

end

section

namespace WeldedPath.Supplement.EdgeBookkeeping

open Classical LoopProof KappaKernel CrossingExclusion
open scoped BigOperators









def ColoredAdj {n : ℕ} (H : AbsForest n) (u v : Fin H.k) (α : Fin 3) : Prop :=
  ∃ p ∈ H.E, H.color p = α ∧ ((p.1 = u ∧ p.2 = v) ∨ (p.1 = v ∧ p.2 = u))







end WeldedPath.Supplement.EdgeBookkeeping

end

section

/- Module: WeldedPathExistingEdgeFibers -/
section

namespace WeldedPath.Supplement.EdgeBookkeeping

open Classical AssignmentDatabase DatabaseSupport DatabaseReadout
open WeldedPath.UniformFiberEncoding

variable {n l : ℕ} {G : WeldedInstance n}

def ExistingInput (l : ℕ) (G : WeldedInstance n) (H : AbsForest n) (a : Fin H.k) (α : Fin 3) :=
  {z : SupportedAssignment l G H × (Fin H.k × Fin H.k) //
    z.2.1 < z.2.2 ∧ FreshColor H z.2.1 α ∧ FreshColor H z.2.2 α ∧
    kappa l G α (z.1.val z.2.1).val (z.1.val z.2.2).val ≠ 0 ∧ (a = z.2.1 ∨ a = z.2.2)}

noncomputable instance (H : AbsForest n) (a : Fin H.k) (α : Fin 3) :
    Fintype (ExistingInput l G H a α) := inferInstanceAs (Fintype {z : SupportedAssignment l G H × (Fin H.k × Fin H.k) // _})







end WeldedPath.Supplement.EdgeBookkeeping
end

/- Module: WeldedPathExistingEdgeNorm -/
section

namespace WeldedPath.Supplement.EdgeBookkeeping

open Classical AssignmentDatabase DatabaseSupport KappaKernel EdgePotential ReciprocalClasses
open WeldedPath.UniformFiberEncoding WeldedPath.WeightedCoefficients
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}











end WeldedPath.Supplement.EdgeBookkeeping
end

/- Module: WeldedPathRootSourceWeight -/
section

namespace WeldedPath.Supplement.EdgePotential

open Classical ConnectedConcentration DescriptionCoefficients SourceFiberBound
open FixedDataFunctions CoefficientDecomposition KappaKernel EdgeBookkeeping
open WeldedPath.WeightedCoefficients
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}

/-- One weight realizes all source fibers rooted at the same vertex. -/
noncomputable def rootSourceWeight (l : ℕ) (G : WeldedInstance n)
    (H : AbsForest n) (a : Fin H.k) (B : Finset ℕ) (φ : Fin H.k → Label n) : ℝ :=
  sourceWeight l G H φ a B φ

theorem rootSourceWeight_nonneg (H : AbsForest n) (hH : H.IsValid)
    (a : Fin H.k) (B : Finset ℕ) (φ : Fin H.k → Label n) :
    0 ≤ rootSourceWeight l G H a B φ := by
  unfold rootSourceWeight sourceWeight
  split_ifs
  · exact ForestFactorization.muRef_nonneg l G H hH φ
  · rfl

theorem rootSourceWeight_fiber (H : AbsForest n) (a : Fin H.k) (B : Finset ℕ)
    (φ₀ φ : Fin H.k → Label n) :
    (if H.Wfix φ a = H.Wfix φ₀ a then rootSourceWeight l G H a B φ else 0) =
      sourceWeight l G H φ₀ a B φ := by
  unfold rootSourceWeight sourceWeight
  by_cases hd : H.Wfix φ a = H.Wfix φ₀ a
  · simp only [hd, eq_self, true_and, if_true]
  · simp only [hd, false_and, if_false]

theorem rootSourceWeight_source (H : AbsForest n) (a : Fin H.k) (B : Finset ℕ)
    (φ₀ : Fin H.k → Label n) (hpos : 0 < rootSourceWeight l G H a B φ₀) :
    H.muRef l G φ₀ ≠ 0 ∧ ∀ φ,
      (if H.Wfix φ a = H.Wfix φ₀ a then rootSourceWeight l G H a B φ else 0) =
        sourceWeight l G H φ₀ a B φ := by
  refine ⟨?_, rootSourceWeight_fiber H a B φ₀⟩
  unfold rootSourceWeight sourceWeight at hpos
  split_ifs at hpos
  · exact ne_of_gt hpos
  · exact (lt_irrefl 0 hpos).elim

theorem sourceAmplitude_eq_root_fiber (H : AbsForest n) (a : Fin H.k) (B : Finset ℕ)
    (φ₀ : Fin H.k → Label n) :
    sourceAmplitude l G H B a φ₀ =
      fiberAmplitude (rootSourceWeight l G H a B) (fun φ => H.Wfix φ a) (H.Wfix φ₀ a) := by
  ext φ
  change (Real.sqrt (sourceWeight l G H φ₀ a B φ) : ℂ) =
    (Real.sqrt (rootSourceWeight l G H a B φ) : ℂ) *
      (if H.Wfix φ a = H.Wfix φ₀ a then 1 else 0)
  rw [← rootSourceWeight_fiber H a B φ₀ φ]
  split_ifs <;> simp

theorem root_source_span_le_dataSpace (H : AbsForest n) (a : Fin H.k) (B : Finset ℕ) :
    Submodule.span ℂ {f | ∃ φ₀, f = sourceAmplitude l G H B a φ₀} ≤
      dataSpace (rootSourceWeight l G H a B) (fun φ => H.Wfix φ a) := by
  apply Submodule.span_le.mpr
  rintro f ⟨φ₀, rfl⟩
  rw [sourceAmplitude_eq_root_fiber]
  exact ⟨(fun d => if d = H.Wfix φ₀ a then 1 else 0), rfl⟩



end WeldedPath.Supplement.EdgePotential
end

/- Module: WeldedPathExistingSourceBounds -/
section

namespace WeldedPath.Supplement.EdgeBookkeeping

open Classical DatabaseSupport DescriptionCoefficients KappaKernel EdgePotential
open WeldedPath.UniformFiberEncoding
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}



end WeldedPath.Supplement.EdgeBookkeeping
end

end

section

namespace WeldedPath.Supplement.BoundaryAdjustment

open Classical EdgePotential SourceFiberBound ConnectedConcentration FixedDataFunctions
open WeldedPath.WeightedCoefficients WeldedPath.HilbertSupport
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}

theorem outside_hit_iff_free (H : AbsForest n) (a v : Fin H.k) (R : Finset ℕ)
    (hRw : Disjoint R (Vweld n)) (φ : Fin H.k → Label n) :
    (v ∉ H.Ctree φ a ∧ (φ v).val ∈ R) ↔ (v ∉ H.Sfix φ a ∧ (φ v).val ∈ R) := by
  constructor
  · rintro ⟨ht,hr⟩
    refine ⟨fun hs => ?_,hr⟩
    exact Finset.disjoint_left.mp hRw hr (weld_of_mem_sfix_not_ctree H φ a v hs ht)
  · rintro ⟨hs,hr⟩
    exact ⟨fun ht => hs (FixedData.ctree_subset_sfix H φ a ht),hr⟩

theorem label_hit_card_le (R : Finset ℕ) :
    Fintype.card {x : Label n // x.val ∈ R} ≤ R.card := by
  let f : {x : Label n // x.val ∈ R} → R := fun x => ⟨x.val.val,x.property⟩
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply Fin.ext
    exact congrArg Subtype.val h
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hf

/-- A new boundary label outside the selected tree is a genuinely free label:
fixed vertices across the weld are excluded by disjointness from the weld. -/
theorem outside_hit_norm_sq_le (H : AbsForest n) (hH : H.IsValid)
    (mu : (Fin H.k → Label n) → ℝ) (hmu : ∀ φ,0 ≤ mu φ)
    (a : Fin H.k) (ha : ∀ u,H.graph.Reachable a u)
    (hG : G.IsValid) (hn : 16 ≤ n) (hl : 2 ≤ l) (hln : l ≤ n-4)
    (B : Finset ℕ) (hB : Vbd n l ⊆ B) (hBw : Disjoint B (Vweld n))
    (hsmall : (H.k : ℝ)*(B.card : ℝ)*(4/(2:ℝ)^n) ≤ 1/2)
    (hsource : ∀ φ₀,0 < mu φ₀ → H.muRef l G φ₀ ≠ 0 ∧ ∀ φ,
      (if H.Wfix φ a = H.Wfix φ₀ a then mu φ else 0) = sourceWeight l G H φ₀ a B φ)
    (R : Finset ℕ) (hRw : Disjoint R (Vweld n)) (v : Fin H.k)
    (f : Hil (Fin H.k → Label n)) (hf : f ∈ dataSpace mu (fun φ => H.Wfix φ a)) :
    ‖(eventSpace (fun φ => v ∉ H.Ctree φ a ∧ (φ v).val ∈ R)).starProjection f‖^2 ≤
      (8*(R.card : ℝ)/(2:ℝ)^n)*‖f‖^2 := by
  let Y := {x : Label n // x.val ∈ R}
  let P : Y → (Fin H.k → Label n) → Prop := fun x φ => v ∉ H.Sfix φ a ∧ φ v=x.val
  have he : (fun φ => v ∉ H.Ctree φ a ∧ (φ v).val ∈ R) = (fun φ => ∃ x : Y,P x φ) := by
    funext φ
    apply propext
    rw [outside_hit_iff_free H a v R hRw φ]
    constructor
    · rintro ⟨hv,hr⟩
      exact ⟨⟨φ v,hr⟩,hv,rfl⟩
    · rintro ⟨x,hv,hx⟩
      exact ⟨hv,hx.symm ▸ x.property⟩
  obtain ⟨c,hc⟩ := (mem_dataSpace mu (fun φ => H.Wfix φ a) f).mp hf
  have hp (x : Y) : ‖(eventSpace (P x)).starProjection f‖^2 ≤ (8/(2:ℝ)^n)*‖f‖^2 := by
    rw [← hc]
    apply conditional_event_bound mu hmu (fun φ => H.Wfix φ a) (P x) (8/(2:ℝ)^n) _ c
    intro d
    exact free_point_fiber_bound H hH mu hmu a ha hG hn hl hln B hB hBw hsmall hsource v x.val d
  rw [he]
  calc
    _ ≤ ∑ x : Y,‖(eventSpace (P x)).starProjection f‖^2 := event_union_norm_sq P f
    _ ≤ ∑ _x : Y,(8/(2:ℝ)^n)*‖f‖^2 := Finset.sum_le_sum fun x _ => hp x
    _ = (Fintype.card Y : ℝ)*((8/(2:ℝ)^n)*‖f‖^2) := by simp
    _ ≤ (R.card : ℝ)*((8/(2:ℝ)^n)*‖f‖^2) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast label_hit_card_le (n:=n) R) (by positivity)
    _ = _ := by ring

noncomputable def outsideHits (H : AbsForest n) (a : Fin H.k) (R : Finset ℕ)
    (φ : Fin H.k → Label n) : ℕ :=
  (Finset.univ.filter (fun v => v ∉ H.Ctree φ a ∧ (φ v).val ∈ R)).card

theorem outsideHits_energy (H : AbsForest n) (a : Fin H.k) (R : Finset ℕ)
    (f : Hil (Fin H.k → Label n)) :
    (∑ φ,(outsideHits H a R φ : ℝ)*‖f φ‖^2) =
      ∑ v : Fin H.k,‖(eventSpace (fun φ => v ∉ H.Ctree φ a ∧ (φ v).val ∈ R)).starProjection f‖^2 := by
  simp only [eventSpace_projection,EuclideanSpace.norm_sq_eq]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro φ _
  simp only [diagProj_apply]
  simp only [apply_ite (fun z : ℂ => ‖z‖^2), norm_zero, zero_pow (by decide : 2 ≠ 0)]
  rw [← Finset.sum_filter]
  simp only [outsideHits,Finset.sum_const,nsmul_eq_mul]

/-- This is the vertex-count version of the conditional marked-tree estimate
in source Eq. 72; the number of other marked tree components is no larger. -/
theorem outsideHits_energy_le (H : AbsForest n) (hH : H.IsValid)
    (mu : (Fin H.k → Label n) → ℝ) (hmu : ∀ φ,0 ≤ mu φ)
    (a : Fin H.k) (ha : ∀ u,H.graph.Reachable a u)
    (hG : G.IsValid) (hn : 16 ≤ n) (hl : 2 ≤ l) (hln : l ≤ n-4)
    (B : Finset ℕ) (hB : Vbd n l ⊆ B) (hBw : Disjoint B (Vweld n))
    (hsmall : (H.k : ℝ)*(B.card : ℝ)*(4/(2:ℝ)^n) ≤ 1/2)
    (hsource : ∀ φ₀,0 < mu φ₀ → H.muRef l G φ₀ ≠ 0 ∧ ∀ φ,
      (if H.Wfix φ a = H.Wfix φ₀ a then mu φ else 0) = sourceWeight l G H φ₀ a B φ)
    (R : Finset ℕ) (hRw : Disjoint R (Vweld n))
    (f : Hil (Fin H.k → Label n)) (hf : f ∈ dataSpace mu (fun φ => H.Wfix φ a)) :
    (∑ φ,(outsideHits H a R φ : ℝ)*‖f φ‖^2) ≤
      ((H.k : ℝ)*8*(R.card : ℝ)/(2:ℝ)^n)*‖f‖^2 := by
  rw [outsideHits_energy]
  calc
    _ ≤ ∑ _v : Fin H.k,(8*(R.card : ℝ)/(2:ℝ)^n)*‖f‖^2 := Finset.sum_le_sum fun v _ =>
      outside_hit_norm_sq_le H hH mu hmu a ha hG hn hl hln B hB hBw hsmall hsource R hRw v f hf
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

end WeldedPath.Supplement.BoundaryAdjustment

end

section

namespace WeldedPath.Supplement.BoundaryAdjustment

open Classical EdgePotential ConnectedConcentration DescriptionCoefficients FixedDataFunctions
open AllBoundaryStability FixedData FixedCollisions
open WeldedPath.WeightedCoefficients WeldedPath.HilbertSupport
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}

/-- The new boundary is avoided outside the selected tree in its component. -/
def avoidsOutside (H : AbsForest n) (a : Fin H.k) (R : Finset ℕ)
    (φ : Fin H.k → Label n) : Prop :=
  ∀ u,H.graph.Reachable a u → u ∉ H.Ctree φ a → (φ u).val ∉ R

noncomputable def boundaryMask (H : AbsForest n) (a : Fin H.k) (R : Finset ℕ) :
    Hil (Fin H.k → Label n) →L[ℂ] Hil (Fin H.k → Label n) :=
  diagProj (avoidsOutside H a R)

/-- The actual canonical fixed-root source space, with all reference fibers. -/
noncomputable def rootSourceSpace (l : ℕ) (G : WeldedInstance n)
    (H : AbsForest n) (B : Finset ℕ) (a : Fin H.k) :
    Submodule ℂ (Hil (Fin H.k → Label n)) :=
  Submodule.span ℂ {f | ∃ φ₀,f = sourceAmplitude l G H B a φ₀}


theorem sourceWeight_union (H : AbsForest n) (a : Fin H.k) (B R : Finset ℕ)
    (φ₀ φ : Fin H.k → Label n) :
    sourceWeight l G H φ₀ a (B ∪ R) φ =
      if avoidsOutside H a R φ then sourceWeight l G H φ₀ a B φ else 0 := by
  unfold sourceWeight
  by_cases hR : avoidsOutside H a R φ
  · rw [if_pos hR]
    congr 1
    apply propext
    constructor
    · rintro ⟨he,h⟩
      exact ⟨he,fun u hu ht hb => h u hu ht (Finset.mem_union_left R hb)⟩
    · rintro ⟨he,h⟩
      refine ⟨he,?_⟩
      intro u hu ht hr
      rcases Finset.mem_union.mp hr with hb | hr
      · exact h u hu ht hb
      · exact hR u hu ht hr
  · rw [if_neg hR]
    apply if_neg
    rintro ⟨_,h⟩
    apply hR
    intro u hu ht hr
    exact h u hu ht (Finset.mem_union_right B hr)


theorem sourceAmplitude_union (H : AbsForest n) (a : Fin H.k) (B R : Finset ℕ)
    (φ₀ : Fin H.k → Label n) :
    sourceAmplitude l G H (B ∪ R) a φ₀ = boundaryMask H a R (sourceAmplitude l G H B a φ₀) := by
  ext φ
  simp only [boundaryMask,diagProj_apply]
  change (Real.sqrt (sourceWeight l G H φ₀ a (B ∪ R) φ) : ℂ) =
    if avoidsOutside H a R φ then (Real.sqrt (sourceWeight l G H φ₀ a B φ) : ℂ) else 0
  rw [sourceWeight_union]
  split_ifs <;> simp only [Real.sqrt_zero,Complex.ofReal_zero]

/-- Exact image identity, with the original reference measure and all its
normalizers retained. No parameter bounds or validity assumptions are needed. -/
theorem rootSourceSpace_union (H : AbsForest n) (a : Fin H.k) (B R : Finset ℕ) :
    rootSourceSpace l G H (B ∪ R) a =
      (rootSourceSpace l G H B a).map (boundaryMask H a R).toLinearMap := by
  unfold rootSourceSpace
  rw [Submodule.map_span]
  congr 1
  ext f
  constructor
  · rintro ⟨φ₀,rfl⟩
    exact ⟨sourceAmplitude l G H B a φ₀,⟨φ₀,rfl⟩,(sourceAmplitude_union H a B R φ₀).symm⟩
  · rintro ⟨g,⟨φ₀,rfl⟩,rfl⟩
    exact ⟨φ₀,(sourceAmplitude_union H a B R φ₀).symm⟩

theorem rootSourceSpace_eq_dataSpace (H : AbsForest n) (a : Fin H.k) (B : Finset ℕ) :
    rootSourceSpace l G H B a = dataSpace (rootSourceWeight l G H a B) (fun φ => H.Wfix φ a) := by
  apply le_antisymm (root_source_span_le_dataSpace H a B)
  intro f hf
  obtain ⟨h,rfl⟩ := (mem_dataSpace _ _ f).mp hf
  rw [lift_eq_sum_fibers]
  apply Submodule.sum_mem
  intro d hd
  obtain ⟨φ₀,_,rfl⟩ := Finset.mem_image.mp hd
  apply Submodule.smul_mem
  rw [← sourceAmplitude_eq_root_fiber]
  exact Submodule.subset_span ⟨φ₀,rfl⟩

theorem allSectorSpace_eq_iSup_rootSourceSpace (H : AbsForest n) (hH : H.IsValid)
    (B : Finset ℕ) (hconn : ∀ v u,H.graph.Reachable v u) :
    allSectorSpace l G H B = ⨆ a,rootSourceSpace l G H B a := by
  rw [allSectorSpace_eq_connectedSpan l G H hH B hconn]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro f ⟨a,φ₀,rfl⟩
    exact (le_iSup (fun a => rootSourceSpace l G H B a) a)
      (Submodule.subset_span ⟨φ₀,rfl⟩)
  · apply iSup_le
    intro a
    apply Submodule.span_le.mpr
    rintro f ⟨φ₀,rfl⟩
    exact Submodule.subset_span ⟨a,φ₀,rfl⟩

/-- Whether the selected tree itself meets the new boundary is fixed-data
measurable, unlike the event that another tree meets the new boundary. -/
def treeHit (H : AbsForest n) (a : Fin H.k) (R : Finset ℕ)
    (φ : Fin H.k → Label n) : Prop := ∃ u ∈ H.Ctree φ a,(φ u).val ∈ R

theorem treeHit_factors (H : AbsForest n) (hH : H.IsValid) (a : Fin H.k) (R : Finset ℕ) :
    Function.FactorsThrough (treeHit H a R) (fun φ => H.Wfix φ a) := by
  intro φ ψ hd
  apply propext
  have ht : H.Ctree φ a = H.Ctree ψ a := congrArg Prod.fst hd
  have hv := (wfix_eq_iff_agree_sfix H hH φ ψ a).mp hd
  constructor
  · rintro ⟨u,hu,hr⟩
    have hu' : u ∈ H.Ctree ψ a := ht ▸ hu
    refine ⟨u,hu',?_⟩
    rw [← hv u (ctree_subset_sfix H ψ a hu')]
    exact hr
  · rintro ⟨u,hu,hr⟩
    refine ⟨u,ht.symm ▸ hu,?_⟩
    rw [hv u (ctree_subset_sfix H ψ a hu)]
    exact hr

theorem treeHit_mask_mem_rootSourceSpace (H : AbsForest n) (hH : H.IsValid)
    (a : Fin H.k) (B R : Finset ℕ) (f : Hil (Fin H.k → Label n))
    (hf : f ∈ rootSourceSpace l G H B a) :
    (eventSpace (treeHit H a R)).starProjection f ∈ rootSourceSpace l G H B a := by
  rw [rootSourceSpace_eq_dataSpace] at hf ⊢
  exact dataSpace_mask_closed _ _ _ (treeHit_factors H hH a R) f hf

theorem not_avoidsOutside_iff (H : AbsForest n) (a : Fin H.k)
    (ha : ∀ u,H.graph.Reachable a u) (R : Finset ℕ) (φ : Fin H.k → Label n) :
    ¬avoidsOutside H a R φ ↔ ∃ v,v ∉ H.Ctree φ a ∧ (φ v).val ∈ R := by
  constructor
  · intro h
    by_contra hn
    apply h
    intro v _ ht hr
    exact hn ⟨v,ht,hr⟩
  · rintro ⟨v,ht,hr⟩ h
    exact h v (ha v) ht hr

theorem sub_boundaryMask (H : AbsForest n) (a : Fin H.k) (R : Finset ℕ)
    (f : Hil (Fin H.k → Label n)) :
    f - boundaryMask H a R f = (eventSpace (fun φ => ¬avoidsOutside H a R φ)).starProjection f := by
  rw [eventSpace_projection]
  ext φ
  by_cases h : avoidsOutside H a R φ <;>
    simp only [PiLp.sub_apply,boundaryMask,diagProj_apply,h,not_true_eq_false,
      not_false_eq_true,if_true,if_false,sub_self,sub_zero]


section Quantitative

variable (H : AbsForest n) (hH : H.IsValid) (a : Fin H.k)
  (ha : ∀ u,H.graph.Reachable a u)
  (hG : G.IsValid) (hn : 16 ≤ n) (hl : 2 ≤ l) (hln : l ≤ n-4)
  (B : Finset ℕ) (hB : Vbd n l ⊆ B) (hBw : Disjoint B (Vweld n))
  (hsmall : (H.k : ℝ)*(B.card : ℝ)*(4/(2:ℝ)^n) ≤ 1/2)
  (R : Finset ℕ) (hRw : Disjoint R (Vweld n))

include hH ha hG hn hl hln hB hBw hsmall hRw


theorem rootSourceSpace_outsideHits_energy_le
    (f : Hil (Fin H.k → Label n)) (hf : f ∈ rootSourceSpace l G H B a) :
    (∑ φ,(outsideHits H a R φ : ℝ)*‖f φ‖^2) ≤
      ((H.k : ℝ)*8*(R.card : ℝ)/(2:ℝ)^n)*‖f‖^2 :=
  outsideHits_energy_le H hH (rootSourceWeight l G H a B) (rootSourceWeight_nonneg H hH a B)
    a ha hG hn hl hln B hB hBw hsmall (rootSourceWeight_source H a B) R hRw f
    ((rootSourceSpace_eq_dataSpace H a B).le hf)

theorem rootSourceSpace_boundaryMask_error
    (f : Hil (Fin H.k → Label n)) (hf : f ∈ rootSourceSpace l G H B a) :
    ‖f - boundaryMask H a R f‖^2 ≤ ((H.k : ℝ)*8*(R.card : ℝ)/(2:ℝ)^n)*‖f‖^2 := by
  rw [sub_boundaryMask]
  have he : (fun φ => ¬avoidsOutside H a R φ) =
      (fun φ => ∃ v,v ∉ H.Ctree φ a ∧ (φ v).val ∈ R) := by
    funext φ
    exact propext (not_avoidsOutside_iff H a ha R φ)
  rw [he]
  calc
    _ ≤ ∑ v : Fin H.k,‖(eventSpace (fun φ => v ∉ H.Ctree φ a ∧ (φ v).val ∈ R)).starProjection f‖^2 :=
      event_union_norm_sq _ f
    _ = ∑ φ,(outsideHits H a R φ : ℝ)*‖f φ‖^2 := (outsideHits_energy H a R f).symm
    _ ≤ _ := rootSourceSpace_outsideHits_energy_le H hH a ha hG hn hl hln B hB hBw hsmall R hRw f hf




end Quantitative

end WeldedPath.Supplement.BoundaryAdjustment

end

section

namespace WeldedPath.Supplement.BoundaryAdjustment

open Classical AllBoundaryStability BoundaryCoefficients
open WeldedPath.WeightedCoefficients WeldedPath.HilbertSupport
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}

/-- Distinct tree components containing a vertex mapped into R. -/
noncomputable def markedTrees (H : AbsForest n) (R : Finset ℕ)
    (φ : Fin H.k → Label n) : Finset (Finset (Fin H.k)) :=
  (Finset.univ.filter (fun u => (φ u).val ∈ R)).image (fun u => H.Ctree φ u)

theorem mem_markedTrees (H : AbsForest n) (R : Finset ℕ)
    (φ : Fin H.k → Label n) (T : Finset (Fin H.k)) :
    T ∈ markedTrees H R φ ↔ ∃ u,(φ u).val ∈ R ∧ H.Ctree φ u=T := by
  simp only [markedTrees,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and]

theorem treeHit_iff_mem_markedTrees (H : AbsForest n) (a : Fin H.k) (R : Finset ℕ)
    (φ : Fin H.k → Label n) :
    treeHit H a R φ ↔ H.Ctree φ a ∈ markedTrees H R φ := by
  rw [mem_markedTrees]
  constructor
  · rintro ⟨u,hu,hr⟩
    exact ⟨u,hr,(ctree_eq_of_mem H φ u a hu).symm⟩
  · rintro ⟨u,hr,he⟩
    refine ⟨u,?_,hr⟩
    rw [← he]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,.refl _⟩

theorem markedTrees_eq_empty_iff (H : AbsForest n) (R : Finset ℕ)
    (φ : Fin H.k → Label n) :
    markedTrees H R φ=∅ ↔ ∀ u,(φ u).val ∉ R := by
  constructor
  · intro he u hu
    have hm := (mem_markedTrees H R φ (H.Ctree φ u)).mpr ⟨u,hu,rfl⟩
    rw [he] at hm
    simpa using hm
  · intro h
    apply Finset.ext
    intro T
    constructor
    · intro hT
      obtain ⟨u,hu,_⟩ := (mem_markedTrees H R φ T).mp hT
      exact False.elim (h u hu)
    · intro hT
      exact False.elim (by simpa using hT)

theorem avoidsOutside_iff_markedTrees_subset (H : AbsForest n) (a : Fin H.k)
    (ha : ∀ u,H.graph.Reachable a u) (R : Finset ℕ) (φ : Fin H.k → Label n) :
    avoidsOutside H a R φ ↔ markedTrees H R φ ⊆ {H.Ctree φ a} := by
  constructor
  · intro h T hT
    obtain ⟨u,hu,rfl⟩ := (mem_markedTrees H R φ T).mp hT
    have ht : u ∈ H.Ctree φ a := by
      by_contra ht
      exact h u (ha u) ht hu
    exact Finset.mem_singleton.mpr (ctree_eq_of_mem H φ u a ht).symm
  · intro h u hu ht hr
    have hm := h ((mem_markedTrees H R φ (H.Ctree φ u)).mpr ⟨u,hr,rfl⟩)
    have he := Finset.mem_singleton.mp hm
    apply ht
    rw [← he]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,.refl _⟩

theorem zero_marked_not_treeHit (H : AbsForest n) (a : Fin H.k) (R : Finset ℕ)
    (φ : Fin H.k → Label n) (hz : (markedTrees H R φ).card=0) : ¬treeHit H a R φ := by
  intro hh
  have hm := (treeHit_iff_mem_markedTrees H a R φ).mp hh
  rw [Finset.card_eq_zero.mp hz] at hm
  simpa using hm

theorem avoidsOutside_iff_zero_or_one (H : AbsForest n) (a : Fin H.k)
    (ha : ∀ u,H.graph.Reachable a u) (R : Finset ℕ) (φ : Fin H.k → Label n) :
    avoidsOutside H a R φ ↔ (markedTrees H R φ).card=0 ∨
      ((markedTrees H R φ).card=1 ∧ treeHit H a R φ) := by
  rw [avoidsOutside_iff_markedTrees_subset H a ha R φ]
  constructor
  · intro h
    by_cases hz : markedTrees H R φ=∅
    · exact Or.inl (Finset.card_eq_zero.mpr hz)
    · obtain ⟨T,hT⟩ := Finset.nonempty_iff_ne_empty.mpr hz
      have he : T=H.Ctree φ a := Finset.mem_singleton.mp (h hT)
      have hm : H.Ctree φ a ∈ markedTrees H R φ := he ▸ hT
      have hs : markedTrees H R φ={H.Ctree φ a} :=
        Finset.Subset.antisymm h (Finset.singleton_subset_iff.mpr hm)
      exact Or.inr ⟨by rw [hs]; exact Finset.card_singleton _,
        (treeHit_iff_mem_markedTrees H a R φ).mpr hm⟩
  · rintro (hz | ⟨ho,hh⟩)
    · rw [Finset.card_eq_zero.mp hz]
      exact Finset.empty_subset _
    · obtain ⟨T,hT⟩ := Finset.card_eq_one.mp ho
      have hm := (treeHit_iff_mem_markedTrees H a R φ).mp hh
      rw [hT] at hm ⊢
      exact Finset.singleton_subset_singleton.mpr (Finset.mem_singleton.mp hm).symm

noncomputable def hitProjection (H : AbsForest n) (R : Finset ℕ) (j : ℕ) :
    Hil (Fin H.k → Label n) →L[ℂ] Hil (Fin H.k → Label n) :=
  diagProj (fun φ => (markedTrees H R φ).card=j)

noncomputable def treeMask (H : AbsForest n) (a : Fin H.k) (R : Finset ℕ) :
    Hil (Fin H.k → Label n) →L[ℂ] Hil (Fin H.k → Label n) :=
  (eventSpace (treeHit H a R)).starProjection

theorem treeMask_mem_rootSourceSpace (H : AbsForest n) (hH : H.IsValid)
    (a : Fin H.k) (B R : Finset ℕ) (f : Hil (Fin H.k → Label n))
    (hf : f ∈ rootSourceSpace l G H B a) : treeMask H a R f ∈ rootSourceSpace l G H B a :=
  treeHit_mask_mem_rootSourceSpace H hH a B R f hf

theorem treeMask_idempotent (H : AbsForest n) (a : Fin H.k) (R : Finset ℕ)
    (f : Hil (Fin H.k → Label n)) : treeMask H a R (treeMask H a R f)=treeMask H a R f :=
  (eventSpace (treeHit H a R)).starProjection_eq_self_iff.mpr
    ((eventSpace (treeHit H a R)).starProjection_apply_mem f)

theorem hitProjection_zero_treeMask (H : AbsForest n) (a : Fin H.k) (R : Finset ℕ)
    (f : Hil (Fin H.k → Label n)) : hitProjection H R 0 (treeMask H a R f)=0 := by
  ext φ
  by_cases hz : (markedTrees H R φ).card=0
  · simp only [hitProjection,treeMask,eventSpace_projection,diagProj_apply,if_pos hz,
      if_neg (zero_marked_not_treeHit H a R φ hz),PiLp.zero_apply]
  · simp only [hitProjection,diagProj_apply,if_neg hz,PiLp.zero_apply]

/-- The literal enlarged-boundary mask splits into zero marked components,
or one marked component equal to the selected tree. -/
theorem boundaryMask_decomposition (H : AbsForest n) (a : Fin H.k)
    (ha : ∀ u,H.graph.Reachable a u) (R : Finset ℕ) (f : Hil (Fin H.k → Label n)) :
    boundaryMask H a R f = hitProjection H R 0 f + hitProjection H R 1 (treeMask H a R f) := by
  ext φ
  simp only [boundaryMask,hitProjection,treeMask,eventSpace_projection,diagProj_apply,PiLp.add_apply]
  have hi := avoidsOutside_iff_zero_or_one H a ha R φ
  by_cases hz : (markedTrees H R φ).card=0
  · have ho : ¬(markedTrees H R φ).card=1 := by omega
    simp only [if_pos (hi.mpr (Or.inl hz)),if_pos hz,if_neg ho,add_zero]
  · by_cases ho : (markedTrees H R φ).card=1
    · by_cases hh : treeHit H a R φ
      · simp only [if_pos (hi.mpr (Or.inr ⟨ho,hh⟩)),if_neg hz,if_pos ho,if_pos hh,zero_add]
      · have hn : ¬avoidsOutside H a R φ := fun h => (hi.mp h).elim hz (fun h => hh h.2)
        simp only [if_neg hn,if_neg hz,if_pos ho,if_neg hh,add_zero]
    · have hn : ¬avoidsOutside H a R φ := fun h => (hi.mp h).elim hz (fun h => ho h.1)
      simp only [if_neg hn,if_neg hz,if_neg ho,add_zero]

theorem boundaryMask_marked_piece (H : AbsForest n) (a : Fin H.k)
    (ha : ∀ u,H.graph.Reachable a u) (R : Finset ℕ) (f : Hil (Fin H.k → Label n)) :
    boundaryMask H a R (treeMask H a R f)=hitProjection H R 1 (treeMask H a R f) := by
  rw [boundaryMask_decomposition H a ha R,hitProjection_zero_treeMask,zero_add,treeMask_idempotent]

theorem boundaryMask_zero_piece (H : AbsForest n) (a : Fin H.k)
    (ha : ∀ u,H.graph.Reachable a u) (R : Finset ℕ) (f : Hil (Fin H.k → Label n)) :
    boundaryMask H a R (f-treeMask H a R f)=hitProjection H R 0 f := by
  rw [map_sub,boundaryMask_marked_piece H a ha R,boundaryMask_decomposition H a ha R]
  exact add_sub_cancel_right _ _

noncomputable def markedRootSpace (l : ℕ) (G : WeldedInstance n)
    (H : AbsForest n) (B R : Finset ℕ) (a : Fin H.k) :
    Submodule ℂ (Hil (Fin H.k → Label n)) :=
  (rootSourceSpace l G H B a).map (treeMask H a R).toLinearMap

noncomputable def markedSpace (l : ℕ) (G : WeldedInstance n)
    (H : AbsForest n) (B R : Finset ℕ) : Submodule ℂ (Hil (Fin H.k → Label n)) :=
  ⨆ a,markedRootSpace l G H B R a

theorem markedRootSpace_le_rootSourceSpace (H : AbsForest n) (hH : H.IsValid)
    (B R : Finset ℕ) (a : Fin H.k) : markedRootSpace l G H B R a ≤ rootSourceSpace l G H B a := by
  rintro f ⟨g,hg,rfl⟩
  exact treeMask_mem_rootSourceSpace H hH a B R g hg

theorem markedSpace_le_allSectorSpace (H : AbsForest n) (hH : H.IsValid)
    (B R : Finset ℕ) (hc : ∀ v u,H.graph.Reachable v u) :
    markedSpace l G H B R ≤ allSectorSpace l G H B := by
  rw [allSectorSpace_eq_iSup_rootSourceSpace H hH B hc]
  apply iSup_le
  intro a
  exact (markedRootSpace_le_rootSourceSpace H hH B R a).trans
    (le_iSup (fun a => rootSourceSpace l G H B a) a)

theorem hitProjection_zero_markedSpace (H : AbsForest n) (B R : Finset ℕ)
    (f : Hil (Fin H.k → Label n)) (hf : f ∈ markedSpace l G H B R) :
    hitProjection H R 0 f=0 := by
  have hle : markedSpace l G H B R ≤ LinearMap.ker (hitProjection H R 0).toLinearMap := by
    apply iSup_le
    intro a g hg
    obtain ⟨f,hf,rfl⟩ := hg
    exact hitProjection_zero_treeMask H a R f
  exact hle hf

theorem zero_piece_mem_enlarged_root (H : AbsForest n) (hH : H.IsValid)
    (a : Fin H.k) (ha : ∀ u,H.graph.Reachable a u) (B R : Finset ℕ)
    (f : Hil (Fin H.k → Label n)) (hf : f ∈ rootSourceSpace l G H B a) :
    hitProjection H R 0 f ∈ rootSourceSpace l G H (B ∪ R) a := by
  rw [rootSourceSpace_union]
  exact ⟨f-treeMask H a R f,(rootSourceSpace l G H B a).sub_mem hf
    (treeMask_mem_rootSourceSpace H hH a B R f hf),boundaryMask_zero_piece H a ha R f⟩

theorem one_piece_mem_enlarged_root (H : AbsForest n) (hH : H.IsValid)
    (a : Fin H.k) (ha : ∀ u,H.graph.Reachable a u) (B R : Finset ℕ)
    (f : Hil (Fin H.k → Label n)) (hf : f ∈ markedRootSpace l G H B R a) :
    hitProjection H R 1 f ∈ rootSourceSpace l G H (B ∪ R) a := by
  obtain ⟨g,hg,rfl⟩ := hf
  rw [rootSourceSpace_union]
  exact ⟨treeMask H a R g,treeMask_mem_rootSourceSpace H hH a B R g hg,
    boundaryMask_marked_piece H a ha R g⟩

/-- Exact all-root identification in the connected canonical coefficient
space: the enlarged boundary retains the unmarked old space and the
single-marked part of the marked-root space. -/
theorem allSectorSpace_union_decomposition (H : AbsForest n) (hH : H.IsValid)
    (B R : Finset ℕ) (hc : ∀ v u,H.graph.Reachable v u) :
    allSectorSpace l G H (B ∪ R) =
      (allSectorSpace l G H B).map (hitProjection H R 0).toLinearMap ⊔
      (markedSpace l G H B R).map (hitProjection H R 1).toLinearMap := by
  have hroot (a : Fin H.k) : rootSourceSpace l G H B a ≤ allSectorSpace l G H B := by
    rw [allSectorSpace_eq_iSup_rootSourceSpace H hH B hc]
    exact le_iSup (fun a => rootSourceSpace l G H B a) a
  have hnew (a : Fin H.k) : rootSourceSpace l G H (B ∪ R) a ≤ allSectorSpace l G H (B ∪ R) := by
    rw [allSectorSpace_eq_iSup_rootSourceSpace H hH (B ∪ R) hc]
    exact le_iSup (fun a => rootSourceSpace l G H (B ∪ R) a) a
  apply le_antisymm
  · rw [allSectorSpace_eq_iSup_rootSourceSpace H hH (B ∪ R) hc]
    apply iSup_le
    intro a g hg
    rw [rootSourceSpace_union] at hg
    obtain ⟨f,hf,rfl⟩ := hg
    change boundaryMask H a R f ∈ _
    rw [boundaryMask_decomposition H a (hc a) R]
    apply Submodule.add_mem_sup
    · exact ⟨f,hroot a hf,rfl⟩
    · refine ⟨treeMask H a R f,?_,rfl⟩
      exact (le_iSup (fun a => markedRootSpace l G H B R a) a) ⟨f,hf,rfl⟩
  · apply sup_le
    · rw [Submodule.map_le_iff_le_comap,allSectorSpace_eq_iSup_rootSourceSpace H hH B hc]
      apply iSup_le
      intro a f hf
      exact hnew a (zero_piece_mem_enlarged_root H hH a (hc a) B R f hf)
    · rw [Submodule.map_le_iff_le_comap]
      apply iSup_le
      intro a f hf
      exact hnew a (one_piece_mem_enlarged_root H hH a (hc a) B R f hf)

/-- The two displayed summands have disjoint coordinate supports. -/
theorem decomposition_summands_orthogonal (H : AbsForest n) (B R : Finset ℕ) :
    (allSectorSpace l G H B).map (hitProjection H R 0).toLinearMap ≤
      ((markedSpace l G H B R).map (hitProjection H R 1).toLinearMap)ᗮ := by
  rintro f ⟨x,hx,rfl⟩
  intro g hg
  obtain ⟨y,hy,rfl⟩ := hg
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  apply Finset.sum_eq_zero
  intro φ _
  change (hitProjection H R 0 x) φ * star ((hitProjection H R 1 y) φ)=0
  by_cases hz : (markedTrees H R φ).card=0
  · have ho : ¬(markedTrees H R φ).card=1 := by omega
    simp only [hitProjection,diagProj_apply,if_pos hz,if_neg ho,star_zero,zero_mul,mul_zero]
  · simp only [hitProjection,diagProj_apply,if_neg hz,mul_zero,star_zero,zero_mul]

/-- A marked-root coefficient already satisfies the single-marked estimate
with the actual reference-law loss. Combining different roots without a
root-count loss requires the further marked-representative argument. -/
theorem markedRootSpace_one_error (H : AbsForest n) (hH : H.IsValid)
    (a : Fin H.k) (ha : ∀ u,H.graph.Reachable a u)
    (hG : G.IsValid) (hn : 16 ≤ n) (hl : 2 ≤ l) (hln : l ≤ n-4)
    (B : Finset ℕ) (hB : Vbd n l ⊆ B) (hBw : Disjoint B (Vweld n))
    (hsmall : (H.k : ℝ)*(B.card : ℝ)*(4/(2:ℝ)^n) ≤ 1/2)
    (R : Finset ℕ) (hRw : Disjoint R (Vweld n))
    (f : Hil (Fin H.k → Label n)) (hf : f ∈ markedRootSpace l G H B R a) :
    ‖f-hitProjection H R 1 f‖^2 ≤ ((H.k : ℝ)*8*(R.card : ℝ)/(2:ℝ)^n)*‖f‖^2 := by
  have hroot := markedRootSpace_le_rootSourceSpace H hH B R a hf
  have hm : boundaryMask H a R f=hitProjection H R 1 f := by
    obtain ⟨g,hg,rfl⟩ := hf
    exact boundaryMask_marked_piece H a ha R g
  rw [← hm]
  exact rootSourceSpace_boundaryMask_error H hH a ha hG hn hl hln B hB hBw hsmall R hRw f hroot

end WeldedPath.Supplement.BoundaryAdjustment

end

section

namespace WeldedPath.Supplement.DatabaseSupport

open Classical ForestFactorization FiniteWeightedForest

variable {n l : ℕ} {G : WeldedInstance n}













end WeldedPath.Supplement.DatabaseSupport

end

section

namespace FiniteOrthogonalSectors

open Classical
open scoped BigOperators

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]

/-- The distinct nonzero spaces in a possibly infinite presentation. -/
abbrev Sector (S : ι → Submodule ℂ E) :=
  {P : Submodule ℂ E // P ≠ ⊥ ∧ ∃ i, S i = P}

noncomputable def representative (S : ι → Submodule ℂ E) (P : Sector S) : ι :=
  P.2.2.choose

lemma representative_space (S : ι → Submodule ℂ E) (P : Sector S) :
    S (representative S P) = P.1 := P.2.2.choose_spec

lemma orthogonal (S : ι → Submodule ℂ E)
    (hS : ∀ i j, S i = S j ∨ ∀ x ∈ S i, ∀ y ∈ S j, inner ℂ x y = 0) :
    OrthogonalFamily ℂ (fun P : Sector S => P.1) (fun P => P.1.subtypeₗᵢ) := by
  intro P Q hPQ x y
  obtain h | h := hS (representative S P) (representative S Q)
  · exact False.elim (hPQ (Subtype.ext (by simpa only [representative_space] using h)))
  · apply h x.1 _ y.1 _
    · simpa only [representative_space] using x.2
    · simpa only [representative_space] using y.2




end FiniteOrthogonalSectors

end

section

namespace WeldedPath.Supplement.DatabaseSupport

open Classical

variable {n l : ℕ} {G : WeldedInstance n}















end WeldedPath.Supplement.DatabaseSupport

end

section

namespace WeldedPath.Supplement.EdgeBookkeeping

open Classical KappaKernel KappaWalk DatabaseReadout DatabaseSupport AssignmentDatabase

variable {n l : ℕ} {G : WeldedInstance n}












end WeldedPath.Supplement.EdgeBookkeeping

end

section

namespace WeldedPath.Supplement.EdgeBookkeeping

open Classical KappaKernel DatabaseSupport DatabaseReadout

variable {n l : ℕ} {G : WeldedInstance n}










def ExistingPartner (l : ℕ) (G : WeldedInstance n) (H : AbsForest n) (a : Fin H.k) (α : Fin 3) :=
  {z : SupportedAssignment l G H × Fin H.k // FreshColor H z.2 α ∧
    kappa l G α (z.1.val a).val (z.1.val z.2).val ≠ 0}

noncomputable instance (H : AbsForest n) (a : Fin H.k) (α : Fin 3) :
    Fintype (ExistingPartner l G H a α) := inferInstanceAs (Fintype {z : SupportedAssignment l G H × Fin H.k // _})


end WeldedPath.Supplement.EdgeBookkeeping

end

section

namespace WeldedPath.CompressedPrimitive

open Classical HilbertSupport
open scoped BigOperators















end WeldedPath.CompressedPrimitive

end

section

namespace WeldedPath.CompressedPrimitive

open Classical InjDb Supplement HilbertSupport RegisterTransport EncodedOracleUnitary
open scoped BigOperators ComplexConjugate

variable {s : ℕ}
















end WeldedPath.CompressedPrimitive

end

section

namespace WeldedPath.CompletionLevels

open Classical InjDb
open scoped BigOperators

variable {s : ℕ}




end WeldedPath.CompletionLevels

end

section

namespace WeldedPath.OperatorPolar

open scoped BigOperators
open Classical

variable {X Y : Type*} [Fintype X] [Fintype Y]











end WeldedPath.OperatorPolar

end

section

namespace WeldedPath.IntertwinerPartial

open Classical OperatorPolar HilbertSupport
open scoped BigOperators














end WeldedPath.IntertwinerPartial

end

section

namespace WeldedPath.CompletionLevels

open Classical InjDb HilbertSupport IntertwinerPartial CompressedPrimitive
open scoped BigOperators

variable {s : ℕ}







end WeldedPath.CompletionLevels

end

section

namespace WeldedPath.OperatorPolar

open Classical

set_option maxHeartbeats 1000000

variable {X Y : Type*} [Fintype X] [Fintype Y]







end WeldedPath.OperatorPolar

end

section

namespace WeldedPath.OperatorPolar

open Classical

variable {X Y : Type*} [Fintype X] [Fintype Y]


end WeldedPath.OperatorPolar

end

section

namespace WeldedPath.IntertwinerIsometry

open Classical OperatorPolar CompletionLevels IntertwinerPartial HilbertSupport
open scoped BigOperators








end WeldedPath.IntertwinerIsometry

end

section

namespace WeldedPath.IntertwinerIsometry

open Classical OperatorPolar CompletionLevels IntertwinerPartial HilbertSupport
open scoped BigOperators




end WeldedPath.IntertwinerIsometry

end

section

namespace WeldedPath.CompletionLevels

open Classical InjDb IntertwinerPartial HilbertSupport
open scoped BigOperators

variable {s : ℕ}



end WeldedPath.CompletionLevels

end

section

namespace WeldedPath.RegisterTransport

open Classical Supplement HilbertSupport EncodedOracleUnitary ControlledOperators
open scoped BigOperators

variable {Ω C X Y : Type*} [Fintype Ω] [Fintype C] [Fintype X] [Fintype Y]
  [DecidableEq Ω] [DecidableEq C] [DecidableEq X] [DecidableEq Y]





end WeldedPath.RegisterTransport

end

section

namespace WeldedPath.QueryRunContraction

open Classical QAlgorithms Supplement HilbertSupport RegisterTransport
open scoped BigOperators

variable {A D : Type*} [Fintype A] [Fintype D] [DecidableEq A] [DecidableEq D]






variable {ι κ W : Type*} [Fintype ι] [Fintype κ] [Fintype W]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq W]






end WeldedPath.QueryRunContraction

end

section

namespace WeldedPath.TensorOperators

open Classical EncodedOracleUnitary HilbertSupport
open scoped BigOperators

variable {A X Y Z : Type*} [Fintype A] [Fintype X] [Fintype Y] [Fintype Z]
  [DecidableEq A] [DecidableEq X] [DecidableEq Y]







end WeldedPath.TensorOperators

end

section

namespace WeldedPath.GoodEmpty

open Classical Supplement
open scoped BigOperators












end WeldedPath.GoodEmpty

end

section

namespace WeldedPath.Supplement.CrossingSupport

open Classical HilbertSupport
open scoped BigOperators

set_option maxHeartbeats 400000

variable {n l : ℕ} {G : WeldedInstance n}




end WeldedPath.Supplement.CrossingSupport

end

section

namespace WeldedPath.RunProjection

open Classical QAlgorithms Supplement HilbertSupport RegisterTransport
open QueryRunContraction EncodedOracleUnitary ControlledOperators TensorOperators
open scoped BigOperators

variable {A D : Type*} [Fintype A] [Fintype D] [DecidableEq A] [DecidableEq D]





variable {ι κ W : Type*} [Fintype ι] [Fintype κ] [Fintype W]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq W]










end WeldedPath.RunProjection

end

section

namespace WeldedPath.ControlApproximation

open Classical Supplement HilbertSupport EncodedOracleUnitary ControlledOperators
open RegisterTransport RunProjection TensorOperators
open scoped BigOperators

variable {C X Y : Type*} [Fintype C] [Fintype X] [Fintype Y]
  [DecidableEq C] [DecidableEq X] [DecidableEq Y]





end WeldedPath.ControlApproximation

end

section

namespace WeldedPath.Supplement.LabelInsertion

open Classical LabelBookkeeping AssignmentDatabase DatabaseSupport RegisterTransport CompressedPrimitive
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}









end WeldedPath.Supplement.LabelInsertion

end

section

namespace WeldedPath.Supplement.LabelInsertion

open Classical CompressedPrimitive RegisterTransport HilbertSupport
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}









end WeldedPath.Supplement.LabelInsertion

end

section

namespace WeldedPath.Supplement.LabelInsertion

open Classical CompressedPrimitive RegisterTransport

variable {n l : ℕ} {G : WeldedInstance n}




end WeldedPath.Supplement.LabelInsertion

end

section

namespace WeldedPath.Supplement.LabelInsertion

open Classical QAlgorithms HilbertSupport RegisterTransport ControlledOperators EncodedOracleUnitary ControlApproximation

variable {n l : ℕ} {G : WeldedInstance n}






end WeldedPath.Supplement.LabelInsertion

end

section

namespace WeldedPath.CompressedPrimitive

open Classical Supplement





end WeldedPath.CompressedPrimitive

namespace WeldedPath.RegisterTransport

open Classical Supplement HilbertSupport EncodedOracleUnitary ControlledOperators TensorOperators
open scoped BigOperators

variable {Ω C X : Type*} [Fintype Ω] [Fintype C] [Fintype X]
  [DecidableEq Ω] [DecidableEq C] [DecidableEq X]




end WeldedPath.RegisterTransport

namespace WeldedPath.Supplement.LabelInsertion

open Classical QAlgorithms CompressedPrimitive RegisterTransport

variable {n l : ℕ} {G : WeldedInstance n}




end WeldedPath.Supplement.LabelInsertion


namespace WeldedPath.CompletionLevels

open Classical InjDb IntertwinerPartial HilbertSupport
open scoped BigOperators

variable {s : ℕ}





end WeldedPath.CompletionLevels

end

section

namespace WeldedPath.PartialIsometryContraction

open ContinuousLinearMap

variable {X Y : Type*} [Fintype X] [Fintype Y]


end WeldedPath.PartialIsometryContraction

end

section

namespace WeldedPath.ExactContraction

open Classical QAlgorithms Supplement EncodedOracleUnitary CompressedPrimitive
open scoped BigOperators














end WeldedPath.ExactContraction

end

section

namespace WeldedPath.EdgeRegisterContraction

open Classical QAlgorithms Supplement ExactContraction RegisterTransport HilbertSupport
open scoped BigOperators

variable {n : ℕ}















end WeldedPath.EdgeRegisterContraction

end

section

namespace WeldedPath.RegisterTransport

open Classical Supplement HilbertSupport EncodedOracleUnitary ControlledOperators
open scoped BigOperators

variable {Ω C X : Type*} [Fintype Ω] [Fintype C] [Fintype X]
  [DecidableEq Ω] [DecidableEq C] [DecidableEq X]


end WeldedPath.RegisterTransport

namespace WeldedPath.Supplement.EdgeInsertion

open Classical CompressedPrimitive RegisterTransport EdgeRegisterContraction
open EdgeBookkeeping HilbertSupport EncodedOracleUnitary
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}


















end WeldedPath.Supplement.EdgeInsertion

end

section

namespace WeldedPath.Supplement.EdgeInsertion

open Classical CompressedPrimitive EdgeBookkeeping KappaKernel DatabaseReadout
open HilbertSupport
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}










end WeldedPath.Supplement.EdgeInsertion

end

section

namespace WeldedPath.Supplement.EdgeBookkeeping

open Classical KappaKernel DatabaseReadout DatabaseSupport AssignmentDatabase EdgeInsertion

variable {n l : ℕ} {G : WeldedInstance n}







end WeldedPath.Supplement.EdgeBookkeeping

end

section

/- Module: WeldedPathEdgeFixedOperator -/
section

namespace WeldedPath.Supplement.EdgePotential

open Classical AllSectorLinear CoefficientDecomposition FixedDataFunctions EdgeCoefficientSplit
open EdgeSourceSpan DescriptionCoefficients
open WeldedPath.WeightedCoefficients WeldedPath.CoefficientStability
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}

noncomputable def fOperator (H : AbsForest n) (a : Fin H.k)
    (D : Index H → Hil (Fin H.k → Label n) →ₗ[ℂ] Hil (Fin H.k → Label n)) :
    Hil (Fin H.k → Label n) →ₗ[ℂ] Hil (Fin H.k → Label n) :=
  ∑ i, if treeFixed H a i then D i else 0

theorem fOperator_apply (H : AbsForest n) (a : Fin H.k)
    (D : Index H → Hil (Fin H.k → Label n) →ₗ[ℂ] Hil (Fin H.k → Label n))
    (f : Hil (Fin H.k → Label n)) :
    fOperator H a D f = ∑ i, if treeFixed H a i then D i f else 0 := by
  simp only [fOperator, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> rfl

theorem fOperator_add_gOperator (H : AbsForest n) (a : Fin H.k)
    (D : Index H → Hil (Fin H.k → Label n) →ₗ[ℂ] Hil (Fin H.k → Label n))
    (f : Hil (Fin H.k → Label n)) (hsum : (∑ i, D i f) = f) :
    fOperator H a D f + gOperator H a D f = f := by
  rw [fOperator_apply, gOperator_apply, gPart, ← Finset.sum_add_distrib]
  calc
    _ = ∑ i, D i f := by
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp
    _ = f := hsum


theorem fOperator_source_span (H : AbsForest n) (hH : H.IsValid)
    (a : Fin H.k) (ha : ∀ u, H.graph.Reachable a u) (B : Finset ℕ)
    (D : Index H → Hil (Fin H.k → Label n) →ₗ[ℂ] Hil (Fin H.k → Label n))
    (hD : ∀ i f, D i f ∈ dataSpace (weight l G H B a i) (fun φ => H.Wfix φ (vertex H a i)))
    (hsupp : ∀ i f φ, D i f φ ≠ 0 → (treeFixed H a i ↔ a ∈ H.Ctree φ (vertex H a i)))
    (f : Hil (Fin H.k → Label n)) :
    fOperator H a D f ∈ Submodule.span ℂ {g | ∃ φ₀, g = sourceAmplitude l G H B a φ₀} := by
  rw [fOperator_apply]
  exact fixed_sum_source_span H hH B a ha D hD hsupp f


end WeldedPath.Supplement.EdgePotential
end

/- Module: WeldedPathEdgeGeneratorOperators -/
section

namespace WeldedPath.Supplement.EdgeBookkeeping

open Classical DatabaseSupport DescriptionCoefficients KappaKernel ForestFactorization
open ConnectedConcentration
open WeldedPath.WeightedCoefficients WeldedPath.HilbertSupport
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}

noncomputable abbrev rootDescription (H : AbsForest n) (a : Fin H.k)
    (φ₀ : Fin H.k → Label n) : Description n := ⟨H, {a}, φ₀⟩

theorem rootDescription_valid (H : AbsForest n) (hH : H.IsValid)
    (a : Fin H.k) (ha : ∀ u, H.graph.Reachable a u) (φ₀ : Fin H.k → Label n) :
    (rootDescription H a φ₀).IsValid := by
  refine ⟨hH, ?_⟩
  intro u
  exact ⟨a, ⟨Finset.mem_singleton_self _, (ha u).symm⟩,
    fun s hs => Finset.mem_singleton.mp hs.1⟩

















end WeldedPath.Supplement.EdgeBookkeeping
end

end

section

/- Module: WeldedPathEdgeInsertionSums -/
section

namespace WeldedPath.Supplement.EdgeBookkeeping

open Classical KappaKernel DatabaseReadout DatabaseSupport AssignmentDatabase EdgeInsertion
open ForestFactorization
open WeldedPath.WeightedCoefficients WeldedPath.HilbertSupport
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}













end WeldedPath.Supplement.EdgeBookkeeping
end

/- Module: WeldedPathEdgeLeafRemainder -/
section

namespace WeldedPath.Supplement.EdgeBookkeeping

open Classical DatabaseSupport EdgePotential
open WeldedPath.WeightedCoefficients WeldedPath.HilbertSupport

variable {n l : ℕ} {G : WeldedInstance n}



end WeldedPath.Supplement.EdgeBookkeeping
end

/- Module: WeldedPathEdgeComponentMaps -/
section

namespace WeldedPath.Supplement.EdgePotential

open Classical ComponentForest DisconnectedStability AllSectorLinear DescriptionCoefficients
open WeldedPath.ProductDecomposition WeldedPath.WeightedCoefficients WeldedPath.HilbertSupport
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}

theorem linearTensor_id_tensor {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] (T : Hil X →ₗ[ℂ] Hil X) (f : Hil X) (g : Hil Y) :
    linearTensor T LinearMap.id (ketTensor f g) = ketTensor (T f) g := by
  ext p
  have hc : column (ketTensor f g) p.2 = g p.2 • f := by
    ext x
    change f x*g p.2 = g p.2*f x
    exact mul_comm _ _
  have he := congrArg (fun v : Hil X => v p.1) (linearTensor_column_id T (ketTensor f g) p.2)
  rw [hc,map_smul] at he
  change _ = T f p.1*g p.2
  change _ = g p.2*T f p.1 at he
  exact he.trans (mul_comm _ _)

theorem componentOperator_productAmplitude (H : AbsForest n) (r : Roots H)
    (T : Hil (LocalAssignment H r) →ₗ[ℂ] Hil (LocalAssignment H r))
    (f : (s : Roots H) → Hil (LocalAssignment H s)) :
    componentOperator H r T (productAmplitude H f) =
      productAmplitude H (Function.update f r (T (f r))) := by
  apply (regroupOneHil H r).injective
  change regroupOneHil H r ((regroupOneHil H r).symm
      (linearTensor T LinearMap.id (regroupOneHil H r (productAmplitude H f)))) = _
  rw [(regroupOneHil H r).apply_symm_apply,regroupOne_productAmplitude,
    linearTensor_id_tensor,regroupOne_productAmplitude,Function.update_self]
  congr 1
  ext ψ
  change (∏ s : {s : Roots H // s ≠ r}, f s.val (ψ s)) =
    ∏ s : {s : Roots H // s ≠ r}, (Function.update f r (T (f r))) s.val (ψ s)
  apply Finset.prod_congr rfl
  intro s _
  rw [Function.update_of_ne s.property]

theorem componentOperator_mem_productSpace (H : AbsForest n) (r : Roots H)
    (S U : (s : Roots H) → Submodule ℂ (Hil (LocalAssignment H s)))
    (T : Hil (LocalAssignment H r) →ₗ[ℂ] Hil (LocalAssignment H r))
    (hT : ∀ f ∈ S r,T f ∈ U r) (hother : ∀ s,s ≠ r → S s ≤ U s)
    (f : Hil (Fin H.k → Label n)) (hf : f ∈ productSpace H S) :
    componentOperator H r T f ∈ productSpace H U := by
  have hle : productSpace H S ≤ (productSpace H U).comap (componentOperator H r T) := by
    apply Submodule.span_le.mpr
    rintro v ⟨g,hg,rfl⟩
    change componentOperator H r T (productAmplitude H g) ∈ productSpace H U
    rw [componentOperator_productAmplitude]
    apply Submodule.subset_span
    refine ⟨Function.update g r (T (g r)),?_,rfl⟩
    intro s
    by_cases hs : s = r
    · subst s
      rw [Function.update_self]
      exact hT _ (hg r)
    · rw [Function.update_of_ne hs]
      exact hother s hs (hg s)
  exact hle hf


theorem source_span_le_allSectorSpace (H : AbsForest n) (hH : H.IsValid)
    (a : Fin H.k) (ha : ∀ u,H.graph.Reachable a u) (B : Finset ℕ) :
    Submodule.span ℂ {g | ∃ φ₀,g = sourceAmplitude l G H B a φ₀} ≤
      AllBoundaryStability.allSectorSpace l G H B := by
  rw [allSectorSpace_eq_connectedSpan l G H hH B (fun u v => (ha u).symm.trans (ha v))]
  apply Submodule.span_mono
  rintro g ⟨φ₀,rfl⟩
  exact ⟨a,φ₀,rfl⟩





end WeldedPath.Supplement.EdgePotential
end

/- Module: WeldedPathEdgeSelectedSources -/
section

namespace WeldedPath.Supplement.EdgePotential

open Classical ComponentForest DisconnectedStability AllSectorLinear DescriptionCoefficients
open ForestFactorization
open EdgeBookkeeping WeldedPath.HilbertSupport WeldedPath.WeightedCoefficients
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}












end WeldedPath.Supplement.EdgePotential
end

/- Module: WeldedPathEdgeConnectedInsertion -/
section

namespace WeldedPath.Supplement.EdgeBookkeeping

open Classical DatabaseSupport EdgePotential AllSectorLinear DescriptionCoefficients ComponentForest
open WeldedPath.WeightedCoefficients WeldedPath.UniformFiberEncoding
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}







end WeldedPath.Supplement.EdgeBookkeeping
end

end

section

namespace WeldedPath.Supplement.EdgeBookkeeping

open Classical KappaKernel DatabaseSupport EdgeInsertion ForestFactorization
open WeldedPath.WeightedCoefficients WeldedPath.HilbertSupport WeldedPath.UniformFiberEncoding
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}






end WeldedPath.Supplement.EdgeBookkeeping

end

section

namespace WeldedPath.Supplement.EdgeBookkeeping

open Classical KappaKernel DatabaseSupport ForestFactorization
open WeldedPath.HilbertSupport WeldedPath.WeightedCoefficients
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}






end WeldedPath.Supplement.EdgeBookkeeping

end

section

namespace WeldedPath.Supplement.EdgePotential

open Classical ComponentForest DisconnectedStability AllSectorLinear DescriptionCoefficients
open EdgeBookkeeping ForestFactorization
open WeldedPath.WeightedCoefficients
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}










end WeldedPath.Supplement.EdgePotential

end

section

/- Module: WeldedPathEdgeUpdateSpace -/
section

namespace WeldedPath.Supplement.EdgeBookkeeping

open Classical DatabaseSupport EdgeInsertion
open WeldedPath.HilbertSupport WeldedPath.UniformFiberEncoding
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}








end WeldedPath.Supplement.EdgeBookkeeping
end

/- Module: WeldedPathEdgeJoinError -/
section

namespace WeldedPath.Supplement.EdgeBookkeeping

open Classical KappaKernel EdgePotential DatabaseSupport
open WeldedPath.HilbertSupport WeldedPath.WeightedCoefficients
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}





end WeldedPath.Supplement.EdgeBookkeeping
end

/- Module: WeldedPathEdgeExistingApproximation -/
section

namespace WeldedPath.Supplement.EdgeBookkeeping

open Classical EdgePotential DatabaseSupport KappaKernel
open WeldedPath.HilbertSupport WeldedPath.UniformFiberEncoding
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}



end WeldedPath.Supplement.EdgeBookkeeping
end

/- Module: WeldedPathEdgeLocalSplit -/
section

namespace WeldedPath.Supplement.EdgePotential

open Classical ComponentForest DisconnectedStability AllSectorLinear DescriptionCoefficients
open EdgeBookkeeping CoefficientDecomposition
open WeldedPath.ProductDecomposition WeldedPath.WeightedCoefficients
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}

structure LocalSplit (l : ℕ) (G : WeldedInstance n) (H : AbsForest n)
    (B : Finset ℕ) (a : Fin H.k) where
  fixed : Hil (Fin H.k → Label n) →ₗ[ℂ] Hil (Fin H.k → Label n)
  free : Hil (Fin H.k → Label n) →ₗ[ℂ] Hil (Fin H.k → Label n)
  add : ∀ f ∈ AllBoundaryStability.allSectorSpace l G H B,fixed f + free f = f
  fixed_source : ∀ f,fixed f ∈ Submodule.span ℂ {g | ∃ φ₀,g = sourceAmplitude l G H B a φ₀}
  free_source : ∀ f,free f ∈ Submodule.span ℂ {g | ∃ v φ₀,a ∉ H.Ctree φ₀ v ∧
    g = sourceAmplitude l G H B v φ₀}
  fixed_norm : ∀ f ∈ AllBoundaryStability.allSectorSpace l G H B,‖fixed f‖^2 ≤ ‖f‖^2
  free_norm : ∀ f ∈ AllBoundaryStability.allSectorSpace l G H B,‖free f‖^2 ≤ ‖f‖^2
  free_kernel : ∀ α (x : Label n) f,(∑ φ,kappa l G α (φ a).val x.val * ‖free f φ‖^2) ≤
    (12/(2:ℝ)^n)*‖free f‖^2
  free_potential : ∀ α k f,(∑ φ,potential l G α B k (φ a)*‖free f φ‖^2) ≤
    potentialBudget n B k * ‖free f‖^2


theorem LocalSplit.fixed_mem (H : AbsForest n) (hH : H.IsValid) (a : Fin H.k)
    (ha : ∀ u,H.graph.Reachable a u) (B : Finset ℕ) (L : LocalSplit l G H B a)
    (f : Hil (Fin H.k → Label n)) : L.fixed f ∈ AllBoundaryStability.allSectorSpace l G H B :=
  source_span_le_allSectorSpace H hH a ha B (L.fixed_source f)




end WeldedPath.Supplement.EdgePotential
end

/- Module: WeldedPathEdgeComponentSplit -/
section

namespace WeldedPath.Supplement.EdgePotential

open Classical ComponentForest DisconnectedStability AllSectorLinear DescriptionCoefficients
open EdgeBookkeeping KappaKernel
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}







end WeldedPath.Supplement.EdgePotential
end

/- Module: WeldedPathEdgeDisconnectedInsertion -/
section

namespace WeldedPath.Supplement.EdgeBookkeeping

open Classical EdgePotential ComponentForest DisconnectedStability DatabaseSupport
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}




end WeldedPath.Supplement.EdgeBookkeeping
end

end

section

namespace WeldedPath.Supplement.EdgeDeletionFiber

open Classical InjDb AssignmentDatabase
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}









end WeldedPath.Supplement.EdgeDeletionFiber

end

section

namespace WeldedPath.Supplement.EdgeDeletionFiber

open Classical InjDb CompressedPrimitive EdgeBookkeeping EdgeInsertion
open HilbertSupport RegisterTransport EncodedOracleUnitary UniformFiberEncoding
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}





















end WeldedPath.Supplement.EdgeDeletionFiber

end

section

namespace WeldedPath.Supplement.LabelBookkeeping

open Classical DatabaseSupport

variable {n : ℕ}


























end WeldedPath.Supplement.LabelBookkeeping

end

section

namespace WeldedPath.Supplement.EdgeBookkeeping

open Classical LabelBookkeeping DatabaseSupport

variable {n : ℕ}











end WeldedPath.Supplement.EdgeBookkeeping

end

section

namespace WeldedPath.Supplement.EdgeDeletionFiber

open Classical InjDb CompressedPrimitive EdgeBookkeeping EdgeInsertion AssignmentDatabase
open DatabaseSupport DatabaseReadout LabelInsertion KappaKernel

variable {n l : ℕ} {G : WeldedInstance n}












end WeldedPath.Supplement.EdgeDeletionFiber

end

section

namespace WeldedPath.Supplement.EdgeDeletionFiber

open Classical EdgeBookkeeping EdgeInsertion DatabaseSupport DatabaseReadout
open AssignmentDatabase LabelInsertion KappaKernel HilbertSupport RegisterTransport

variable {n l : ℕ} {G : WeldedInstance n}




end WeldedPath.Supplement.EdgeDeletionFiber

end

section

namespace WeldedPath.Supplement.EdgeDeletionFiber

open Classical EdgeBookkeeping EdgeInsertion DatabaseSupport DatabaseReadout
open AssignmentDatabase LabelInsertion KappaKernel HilbertSupport RegisterTransport ForestFactorization
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}








end WeldedPath.Supplement.EdgeDeletionFiber

end

section

namespace WeldedPath.Supplement.EdgeDeletionFiber

open Classical EdgeBookkeeping EdgeInsertion DatabaseSupport AssignmentDatabase
open LabelInsertion LabelBookkeeping HilbertSupport KappaKernel
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}









end WeldedPath.Supplement.EdgeDeletionFiber

end

section

/- Module: WeldedPathRecoveredSectorOrthogonality -/
section

namespace WeldedPath.Supplement.RecoveredSectors

noncomputable section
open Classical DatabaseSupport HilbertSupport CoefficientStability
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}




end
end WeldedPath.Supplement.RecoveredSectors

end

/- Module: WeldedPathEdgeInsertionRecovery -/
section

namespace WeldedPath.Supplement.EdgeBookkeeping

open Classical DatabaseSupport EdgePotential EdgeInsertion RecoveredSectors ForestFactorization
open WeldedPath.HilbertSupport WeldedPath.WeightedCoefficients
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}





end WeldedPath.Supplement.EdgeBookkeeping
end

/- Module: WeldedPathEdgeFixedCollisionCancellation -/
section

namespace WeldedPath.Supplement.EdgePotential

open Classical AllSectorLinear CoefficientDecomposition DescriptionCoefficients DisconnectedStability
open EdgeBookkeeping DatabaseSupport FixedCollisions FixedDataFunctions
open WeldedPath.WeightedCoefficients WeldedPath.HilbertSupport
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}


theorem masked_part_zero_of_minimal {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (K : Submodule ℂ (Hil Ω)) (P : Ω → Prop) (f x y : Hil Ω)
    (hf : f ∈ Kᗮ) (he : x+y=f)
    (hx : (eventSpace P).starProjection x ∈ K)
    (hxy : inner ℂ ((eventSpace P).starProjection x) ((eventSpace P).starProjection y)=0) :
    (eventSpace P).starProjection x=0 := by
  have hmin := (K.mem_orthogonal f).mp hf _ hx
  have hpp : (eventSpace P).starProjection ((eventSpace P).starProjection x) =
      (eventSpace P).starProjection x :=
    (eventSpace P).starProjection_eq_self_iff.mpr ((eventSpace P).starProjection_apply_mem x)
  have hm : inner ℂ ((eventSpace P).starProjection x) x =
      inner ℂ ((eventSpace P).starProjection x) ((eventSpace P).starProjection x) := by
    rw [← (eventSpace P).inner_starProjection_left_eq_right]
    rw [hpp]
  have hcross : inner ℂ ((eventSpace P).starProjection x) y=0 := by
    rw [← hpp,
      (eventSpace P).inner_starProjection_left_eq_right]
    exact hxy
  rw [← he,inner_add_right,hm,hcross,add_zero] at hmin
  exact inner_self_eq_zero.mp hmin

theorem fOperator_mask_orthogonal_gOperator (H : AbsForest n) (a : Fin H.k)
    (D : Index H → Hil (Fin H.k → Label n) →ₗ[ℂ] Hil (Fin H.k → Label n))
    (horth : ∀ m : Data H → ℂ,∀ i j,i ≠ j → ∀ f g,
      inner ℂ (rootMultiplier H a m (D i f)) (rootMultiplier H a m (D j g))=0)
    (P : (Fin H.k → Label n) → Prop)
    (hP : Function.FactorsThrough P (fun φ => H.Wfix φ a))
    (f : Hil (Fin H.k → Label n)) :
    inner ℂ ((eventSpace P).starProjection (fOperator H a D f))
      ((eventSpace P).starProjection (gOperator H a D f))=0 := by
  obtain ⟨Q,hQ⟩ := (Function.factorsThrough_iff P).mp hP
  have hm (z : Hil (Fin H.k → Label n)) :
      (eventSpace P).starProjection z = rootMultiplier H a (fun d => if Q d then 1 else 0) z := by
    rw [eventSpace_projection]
    ext φ
    simp only [diagProj_apply,rootMultiplier,WithLp.ofLp_toLp]
    have hq := congrFun hQ φ
    change P φ = Q (H.Wfix φ a) at hq
    change (if P φ then z φ else 0) = (if Q (H.Wfix φ a) then 1 else 0)*z φ
    by_cases hp : P φ
    · rw [if_pos hp,if_pos (hq ▸ hp),one_mul]
    · rw [if_neg hp,if_neg (fun h => hp (hq.symm ▸ h)),zero_mul]
  rw [hm,hm,fOperator_apply,gOperator_apply,gPart,map_sum,map_sum,sum_inner]
  apply Finset.sum_eq_zero
  intro i _
  rw [inner_sum]
  apply Finset.sum_eq_zero
  intro j _
  by_cases hi : treeFixed H a i
  · rw [if_pos hi]
    by_cases hj : treeFixed H a j
    · rw [if_pos hj,map_zero,inner_zero_right]
    · rw [if_neg hj]
      exact horth _ i j (fun h => hj (h ▸ hi)) f f
  · rw [if_neg hi,map_zero,inner_zero_left]





end WeldedPath.Supplement.EdgePotential
end

/- Module: WeldedPathEdgeComponentMask -/
section

namespace WeldedPath.Supplement.EdgePotential

open Classical ComponentForest DisconnectedStability AllSectorLinear CoefficientDecomposition FixedDataFunctions
open WeldedPath.WeightedCoefficients WeldedPath.HilbertSupport WeldedPath.ProductDecomposition
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}


theorem componentOperator_column (H : AbsForest n) (r : Roots H)
    (T : Hil (LocalAssignment H r) →ₗ[ℂ] Hil (LocalAssignment H r))
    (f : Hil (Fin H.k → Label n)) (ψ : OneSpectator H r) :
    column (regroupOneHil H r (componentOperator H r T f)) ψ =
      T (column (regroupOneHil H r f) ψ) := by
  have he : regroupOneHil H r (componentOperator H r T f)=
      linearTensor T LinearMap.id (regroupOneHil H r f) :=
    (regroupOneHil H r).apply_symm_apply _
  rw [he,linearTensor_column_id]



end WeldedPath.Supplement.EdgePotential
end


end

section

namespace WeldedPath.Supplement.BoundaryAdjustment

open Classical EdgePotential AllSectorLinear CoefficientDecomposition FixedDataFunctions
open AllBoundaryStability FixedCollisions
open WeldedPath.WeightedCoefficients WeldedPath.HilbertSupport WeldedPath.CoefficientStability
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}

theorem root_hit_factors (H : AbsForest n) (hH : H.IsValid) (a : Fin H.k)
    (R : Finset ℕ) :
    Function.FactorsThrough (fun φ : Fin H.k → Label n => (φ a).val ∈ R)
      (fun φ => H.Wfix φ a) := by
  intro φ ψ he
  have ha : a ∈ H.Sfix ψ a := FixedData.ctree_subset_sfix H ψ a
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _,.refl _⟩)
  have hv := (FixedData.wfix_eq_iff_agree_sfix H hH φ ψ a).mp he a ha
  exact congrArg (fun x : Label n => x.val ∈ R) hv

theorem event_projection_rootMultiplier (H : AbsForest n) (a : Fin H.k)
    (P : (Fin H.k → Label n) → Prop)
    (hP : Function.FactorsThrough P (fun φ => H.Wfix φ a)) :
    ∃ m : Data H → ℂ, ∀ z,
      (eventSpace P).starProjection z = rootMultiplier H a m z := by
  obtain ⟨Q,hQ⟩ := (Function.factorsThrough_iff P).mp hP
  refine ⟨fun d => if Q d then 1 else 0,?_⟩
  intro z
  rw [eventSpace_projection]
  ext φ
  simp only [diagProj_apply,rootMultiplier,WithLp.ofLp_toLp]
  have hq := congrFun hQ φ
  change P φ = Q (H.Wfix φ a) at hq
  change (if P φ then z φ else 0) = (if Q (H.Wfix φ a) then 1 else 0)*z φ
  by_cases hp : P φ
  · rw [if_pos hp,if_pos (hq ▸ hp),one_mul]
  · rw [if_neg hp,if_neg (fun h => hp (hq.symm ▸ h)),zero_mul]

theorem gPart_root_hit_bound (H : AbsForest n) (hH : H.IsValid)
    (a : Fin H.k) (ha : ∀ u,H.graph.Reachable a u)
    (hG : G.IsValid) (hn : 16 ≤ n) (hl : 2 ≤ l) (hln : l ≤ n-4)
    (B : Finset ℕ) (hB : Vbd n l ⊆ B) (hBw : Disjoint B (Vweld n))
    (hsmall : (H.k : ℝ)*(B.card : ℝ)*(4/(2:ℝ)^n) ≤ 1/2)
    (R : Finset ℕ) (hRw : Disjoint R (Vweld n))
    (D : Index H → Hil (Fin H.k → Label n) →ₗ[ℂ] Hil (Fin H.k → Label n))
    (hD : ∀ i f,D i f ∈ dataSpace (weight l G H B a i) (fun φ => H.Wfix φ (vertex H a i)))
    (horth : ∀ m : Data H → ℂ,∀ i j,i ≠ j → ∀ f g,
      inner ℂ (rootMultiplier H a m (D i f)) (rootMultiplier H a m (D j g)) = 0)
    (hsupport : ∀ i f φ,D i f φ ≠ 0 → (treeFixed H a i ↔ a ∈ H.Ctree φ (vertex H a i)))
    (f : Hil (Fin H.k → Label n)) :
    ‖(eventSpace (fun φ => (φ a).val ∈ R)).starProjection (gPart H a D f)‖^2 ≤
      (8*(R.card : ℝ)/(2:ℝ)^n)*‖gPart H a D f‖^2 := by
  let P := fun φ : Fin H.k → Label n => (φ a).val ∈ R
  let v : Index H → Hil (Fin H.k → Label n) := fun i => if treeFixed H a i then 0 else D i f
  obtain ⟨m,hm⟩ := event_projection_rootMultiplier H a P (root_hit_factors H hH a R)
  have hvorth : ∀ m : Data H → ℂ,∀ i j,i ≠ j →
      inner ℂ (rootMultiplier H a m (v i)) (rootMultiplier H a m (v j)) = 0 := by
    intro m i j hij
    dsimp only [v]
    split_ifs <;> first
      | exact horth m i j hij f f
      | simp only [map_zero,inner_zero_left,inner_zero_right]
  have hverr (i : Index H) :
      ‖(eventSpace P).starProjection (v i)‖^2 ≤ (8*(R.card : ℝ)/(2:ℝ)^n)*‖v i‖^2 := by
    by_cases hi : treeFixed H a i
    · simp only [v,if_pos hi,map_zero,norm_zero,zero_pow (by decide : 2 ≠ 0),mul_zero,le_refl]
    · simp only [v,if_neg hi]
      have he : (eventSpace P).starProjection (D i f) =
          (eventSpace (fun φ => a ∉ H.Ctree φ (vertex H a i) ∧ (φ a).val ∈ R)).starProjection (D i f) := by
        ext φ
        by_cases ht : a ∈ H.Ctree φ (vertex H a i)
        · have hz : D i f φ=0 := by
            by_contra hz
            exact hi ((hsupport i f φ hz).mpr ht)
          simp only [eventSpace_projection,diagProj_apply,hz,ite_self]
        · simp only [eventSpace_projection,diagProj_apply,P,ht,not_false_eq_true,true_and]
      rw [he]
      exact outside_hit_norm_sq_le H hH (weight l G H B a i) (weight_nonneg H hH B a i)
        (vertex H a i) (fun u => (ha (vertex H a i)).symm.trans (ha u))
        hG hn hl hln B hB hBw hsmall (ConnectedResolution.weight_source H hH B a ha i)
        R hRw a (D i f) (hD i f)
  change ‖(eventSpace P).starProjection (∑ i,v i)‖^2 ≤ _
  have hpo : ∀ i j,i ≠ j → inner ℂ
      ((eventSpace P).starProjection (v i)) ((eventSpace P).starProjection (v j))=0 := by
    intro i j hij
    rw [hm,hm]
    exact hvorth m i j hij
  rw [map_sum,norm_sum_sq_orthogonal _ hpo]
  calc
    _ ≤ ∑ i,(8*(R.card : ℝ)/(2:ℝ)^n)*‖v i‖^2 := Finset.sum_le_sum fun i _ => hverr i
    _ = (8*(R.card : ℝ)/(2:ℝ)^n)*∑ i,‖v i‖^2 := (Finset.mul_sum _ _ _).symm
    _ = _ := by
      rw [← norm_sum_sq_orthogonal v (fun i j hij => by
        simpa only [rootMultiplier_one] using hvorth (fun _ => 1) i j hij)]
      rfl

theorem marked_complement_root_hit_bound (H : AbsForest n) (hH : H.IsValid)
    (a : Fin H.k) (ha : ∀ u,H.graph.Reachable a u)
    (hG : G.IsValid) (hn : 16 ≤ n) (hl : 2 ≤ l) (hln : l ≤ n-4)
    (B : Finset ℕ) (hB : Vbd n l ⊆ B) (hBw : Disjoint B (Vweld n))
    (hsmall : (H.k : ℝ)*(B.card : ℝ)*(4/(2:ℝ)^n) ≤ 1/2)
    (R : Finset ℕ) (hRw : Disjoint R (Vweld n))
    (f : Hil (Fin H.k → Label n)) (hf : f ∈ allSectorSpace l G H B)
    (hmin : f ∈ (markedSpace l G H B R)ᗮ) :
    ‖(eventSpace (fun φ => (φ a).val ∈ R)).starProjection f‖^2 ≤
      (8*(R.card : ℝ)/(2:ℝ)^n)*‖f‖^2 := by
  obtain ⟨D,hD,hsum,horth,hsupport,hgnorm,_⟩ :=
    edge_potential_resolution H hH a ha hG hn hl hln B hB hBw hsmall
  let P := fun φ : Fin H.k → Label n => (φ a).val ∈ R
  have hfa : fOperator H a D f ∈ rootSourceSpace l G H B a :=
    fOperator_source_span H hH a ha B D hD hsupport f
  have hmask : (eventSpace P).starProjection (fOperator H a D f) ∈ rootSourceSpace l G H B a := by
    rw [rootSourceSpace_eq_dataSpace] at hfa ⊢
    exact dataSpace_mask_closed _ _ P (root_hit_factors H hH a R) _ hfa
  have hk : (eventSpace P).starProjection (fOperator H a D f) ∈ markedSpace l G H B R := by
    apply (le_iSup (fun a => markedRootSpace l G H B R a) a)
    refine ⟨_,hmask,?_⟩
    change treeMask H a R ((eventSpace P).starProjection (fOperator H a D f)) = _
    unfold treeMask
    rw [eventSpace_projection]
    ext φ
    by_cases hp : P φ
    · have hh : treeHit H a R φ := ⟨a,Finset.mem_filter.mpr ⟨Finset.mem_univ _,.refl _⟩,hp⟩
      simp only [eventSpace_projection,diagProj_apply,if_pos hp,if_pos hh]
    · simp only [eventSpace_projection,diagProj_apply,if_neg hp,ite_self]
  have hz := masked_part_zero_of_minimal (markedSpace l G H B R) P f
    (fOperator H a D f) (gOperator H a D f) hmin
    (fOperator_add_gOperator H a D f (hsum f hf)) hk
    (fOperator_mask_orthogonal_gOperator H a D horth P (root_hit_factors H hH a R) f)
  have he : (eventSpace P).starProjection f = (eventSpace P).starProjection (gPart H a D f) := by
    calc
      _ = (eventSpace P).starProjection (fOperator H a D f + gOperator H a D f) :=
        congrArg (fun z => (eventSpace P).starProjection z)
          (fOperator_add_gOperator H a D f (hsum f hf)).symm
      _ = _ := by rw [map_add,hz,zero_add,gOperator_apply]
  change ‖(eventSpace P).starProjection f‖^2 ≤ _
  rw [he]
  exact (gPart_root_hit_bound H hH a ha hG hn hl hln B hB hBw hsmall R hRw D hD horth hsupport f).trans
    (mul_le_mul_of_nonneg_left (hgnorm f hf) (by positivity))

theorem sub_zero_hitProjection (H : AbsForest n) (R : Finset ℕ)
    (f : Hil (Fin H.k → Label n)) :
    f-hitProjection H R 0 f =
      (eventSpace (fun φ => ∃ a : Fin H.k,(φ a).val ∈ R)).starProjection f := by
  ext φ
  have he : (markedTrees H R φ).card=0 ↔ ¬∃ a : Fin H.k,(φ a).val ∈ R := by
    rw [Finset.card_eq_zero,markedTrees_eq_empty_iff]
    simp only [not_exists]
  by_cases hz : (markedTrees H R φ).card=0
  · simp only [PiLp.sub_apply,hitProjection,diagProj_apply,eventSpace_projection,
      if_pos hz,if_neg (he.mp hz),sub_self]
  · have hp : ∃ a : Fin H.k,(φ a).val ∈ R := by
      by_contra hp
      exact hz (he.mpr hp)
    simp only [PiLp.sub_apply,hitProjection,diagProj_apply,eventSpace_projection,
      if_neg hz,if_pos hp,sub_zero]

/-- The complementary half of the connected boundary-adjustment estimate.
The rooted weighted orthogonality prevents any factor for the number of roots. -/
theorem marked_complement_zero_error (H : AbsForest n) (hH : H.IsValid)
    (hc : ∀ v u,H.graph.Reachable v u)
    (hG : G.IsValid) (hn : 16 ≤ n) (hl : 2 ≤ l) (hln : l ≤ n-4)
    (B : Finset ℕ) (hB : Vbd n l ⊆ B) (hBw : Disjoint B (Vweld n))
    (hsmall : (H.k : ℝ)*(B.card : ℝ)*(4/(2:ℝ)^n) ≤ 1/2)
    (R : Finset ℕ) (hRw : Disjoint R (Vweld n))
    (f : Hil (Fin H.k → Label n)) (hf : f ∈ allSectorSpace l G H B)
    (hmin : f ∈ (markedSpace l G H B R)ᗮ) :
    ‖f-hitProjection H R 0 f‖^2 ≤ ((H.k : ℝ)*8*(R.card : ℝ)/(2:ℝ)^n)*‖f‖^2 := by
  rw [sub_zero_hitProjection]
  calc
    _ ≤ ∑ a : Fin H.k,‖(eventSpace (fun φ => (φ a).val ∈ R)).starProjection f‖^2 :=
      event_union_norm_sq _ f
    _ ≤ ∑ _a : Fin H.k,(8*(R.card : ℝ)/(2:ℝ)^n)*‖f‖^2 :=
      Finset.sum_le_sum fun a _ => marked_complement_root_hit_bound H hH a (hc a)
        hG hn hl hln B hB hBw hsmall R hRw f hf hmin
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      ring

end WeldedPath.Supplement.BoundaryAdjustment


end

section

namespace WeldedPath.Supplement.BoundaryAdjustment

open Classical BoundaryCoefficients EdgePotential EdgeSourceSpan
open DescriptionCoefficients ConnectedConcentration
open WeldedPath.WeightedCoefficients WeldedPath.HilbertSupport
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}

def treeRepresentative (H : AbsForest n) (a : Fin H.k)
    (φ : Fin H.k → Label n) : Prop := ∀ b ∈ H.Ctree φ a,a ≤ b

def representativeHit (H : AbsForest n) (a : Fin H.k) (R : Finset ℕ)
    (φ : Fin H.k → Label n) : Prop := treeHit H a R φ ∧ treeRepresentative H a φ

theorem representativeHit_factors (H : AbsForest n) (hH : H.IsValid)
    (a : Fin H.k) (R : Finset ℕ) :
    Function.FactorsThrough (representativeHit H a R) (fun φ => H.Wfix φ a) := by
  intro φ ψ hd
  have ht := treeHit_factors H hH a R hd
  have hc : H.Ctree φ a=H.Ctree ψ a := congrArg Prod.fst hd
  unfold representativeHit treeRepresentative
  rw [ht,hc]

theorem sourceAmplitude_event_projection (H : AbsForest n) (B : Finset ℕ)
    (a : Fin H.k) (φ₀ : Fin H.k → Label n)
    (P : (Fin H.k → Label n) → Prop)
    (hP : Function.FactorsThrough P (fun φ => H.Wfix φ a)) :
    (eventSpace P).starProjection (sourceAmplitude l G H B a φ₀) =
      if P φ₀ then sourceAmplitude l G H B a φ₀ else 0 := by
  rw [sourceAmplitude_eq_root_fiber]
  ext φ
  rw [eventSpace_projection,diagProj_apply]
  change (if P φ then (Real.sqrt (rootSourceWeight l G H a B φ) : ℂ)*
      (if H.Wfix φ a=H.Wfix φ₀ a then 1 else 0) else 0) = _
  by_cases hd : H.Wfix φ a=H.Wfix φ₀ a
  · have hp : P φ=P φ₀ := hP hd
    by_cases h₀ : P φ₀ <;> simp only [hp,h₀,if_true,if_false,
      fiberAmplitude,lift,WithLp.ofLp_toLp,PiLp.zero_apply,hd]
  · by_cases h₀ : P φ₀ <;> simp only [h₀,if_true,if_false,
      fiberAmplitude,lift,WithLp.ofLp_toLp,PiLp.zero_apply,hd,mul_zero,ite_self]

noncomputable def representativeRootSpace (l : ℕ) (G : WeldedInstance n)
    (H : AbsForest n) (B R : Finset ℕ) (a : Fin H.k) :
    Submodule ℂ (Hil (Fin H.k → Label n)) :=
  Submodule.span ℂ {f | ∃ φ₀,representativeHit H a R φ₀ ∧
    f=sourceAmplitude l G H B a φ₀}

theorem representativeRootSpace_le_rootSourceSpace (H : AbsForest n) (B R : Finset ℕ)
    (a : Fin H.k) : representativeRootSpace l G H B R a ≤ rootSourceSpace l G H B a := by
  apply Submodule.span_le.mpr
  rintro f ⟨φ₀,hφ₀,rfl⟩
  exact Submodule.subset_span ⟨φ₀,rfl⟩

theorem representativeRootSpace_mask (H : AbsForest n) (hH : H.IsValid)
    (B R : Finset ℕ) (a : Fin H.k) (f : Hil (Fin H.k → Label n))
    (hf : f ∈ representativeRootSpace l G H B R a) :
    (eventSpace (representativeHit H a R)).starProjection f=f := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨φ₀,hφ₀,rfl⟩ := hf
      rw [sourceAmplitude_event_projection H B a φ₀ _ (representativeHit_factors H hH a R),if_pos hφ₀]
  | zero => exact map_zero _
  | add f g _ _ hf hg => rw [map_add,hf,hg]
  | smul c f _ hf => rw [map_smul,hf]

theorem representativeRootSpace_support (H : AbsForest n) (hH : H.IsValid)
    (B R : Finset ℕ) (a : Fin H.k) (f : Hil (Fin H.k → Label n))
    (hf : f ∈ representativeRootSpace l G H B R a)
    (φ : Fin H.k → Label n) (hne : f φ ≠ 0) : representativeHit H a R φ := by
  have he := congrArg (fun z : Hil (Fin H.k → Label n) => z φ)
    (representativeRootSpace_mask H hH B R a f hf)
  rw [eventSpace_projection,diagProj_apply] at he
  by_contra hn
  rw [if_neg hn] at he
  exact hne he.symm

theorem representativeRootSpace_le_markedRootSpace (H : AbsForest n) (hH : H.IsValid)
    (B R : Finset ℕ) (a : Fin H.k) :
    representativeRootSpace l G H B R a ≤ markedRootSpace l G H B R a := by
  apply Submodule.span_le.mpr
  rintro f ⟨φ₀,hφ₀,rfl⟩
  refine ⟨sourceAmplitude l G H B a φ₀,Submodule.subset_span ⟨φ₀,rfl⟩,?_⟩
  exact (sourceAmplitude_event_projection H B a φ₀ _ (treeHit_factors H hH a R)).trans (if_pos hφ₀.1)

theorem markedSpace_eq_representativeSup (H : AbsForest n) (hH : H.IsValid)
    (hc : ∀ v u,H.graph.Reachable v u) (B R : Finset ℕ) :
    markedSpace l G H B R=⨆ a,representativeRootSpace l G H B R a := by
  apply le_antisymm
  · apply iSup_le
    intro a f hf
    obtain ⟨g,hg,rfl⟩ := hf
    induction hg using Submodule.span_induction with
    | mem g hg =>
        obtain ⟨φ₀,rfl⟩ := hg
        change (eventSpace (treeHit H a R)).starProjection _ ∈ _
        rw [sourceAmplitude_event_projection H B a φ₀ _ (treeHit_factors H hH a R)]
        split_ifs with hh
        · have hne : (H.Ctree φ₀ a).Nonempty :=
            ⟨a,Finset.mem_filter.mpr ⟨Finset.mem_univ _,.refl _⟩⟩
          let b := (H.Ctree φ₀ a).min' hne
          have hb : b ∈ H.Ctree φ₀ a := Finset.min'_mem _ _
          have hc' := ctree_eq_of_mem H φ₀ b a hb
          rw [sourceAmplitude_reroot H hH B b a hc φ₀ hb]
          apply (le_iSup (fun a => representativeRootSpace l G H B R a) b)
          apply Submodule.subset_span
          refine ⟨φ₀,⟨?_,?_⟩,rfl⟩
          · obtain ⟨u,hu,hr⟩ := hh
            exact ⟨u,hc' ▸ hu,hr⟩
          · intro u hu
            exact Finset.min'_le _ u (hc'.symm ▸ hu)
        · exact Submodule.zero_mem _
    | zero => simpa only [map_zero] using (⨆ a,representativeRootSpace l G H B R a).zero_mem
    | add f g _ _ hf hg => simpa only [map_add] using
        (⨆ a,representativeRootSpace l G H B R a).add_mem hf hg
    | smul c f _ hf => simpa only [map_smul] using
        (⨆ a,representativeRootSpace l G H B R a).smul_mem c hf
  · apply iSup_le
    intro a
    exact (representativeRootSpace_le_markedRootSpace H hH B R a).trans
      (le_iSup (fun a => markedRootSpace l G H B R a) a)

theorem markedSpace_representative_decomposition (H : AbsForest n) (hH : H.IsValid)
    (hc : ∀ v u,H.graph.Reachable v u) (B R : Finset ℕ)
    (f : Hil (Fin H.k → Label n)) (hf : f ∈ markedSpace l G H B R) :
    ∃ v : Fin H.k → Hil (Fin H.k → Label n),
      (∀ a,v a ∈ representativeRootSpace l G H B R a) ∧ (∑ a,v a)=f := by
  rw [markedSpace_eq_representativeSup H hH hc B R] at hf
  have hf' : f ∈ ⨆ a ∈ (Finset.univ : Finset (Fin H.k)),representativeRootSpace l G H B R a := by
    simpa only [Finset.mem_univ,iSup_true] using hf
  obtain ⟨v,hv⟩ := (Submodule.mem_iSup_finset_iff_exists_sum
    (fun a => representativeRootSpace l G H B R a) f).mp hf'
  exact ⟨fun a => v a,fun a => (v a).property,by simpa using hv⟩

theorem representative_same_tree (H : AbsForest n) (φ : Fin H.k → Label n)
    (a b : Fin H.k) (ha : treeRepresentative H a φ) (hb : treeRepresentative H b φ)
    (he : H.Ctree φ a=H.Ctree φ b) : a=b := by
  have ha' : a ∈ H.Ctree φ a := Finset.mem_filter.mpr ⟨Finset.mem_univ _,.refl _⟩
  have hb' : b ∈ H.Ctree φ b := Finset.mem_filter.mpr ⟨Finset.mem_univ _,.refl _⟩
  exact le_antisymm (ha b (he.symm ▸ hb')) (hb a (he ▸ ha'))

theorem representative_unique_at_one (H : AbsForest n) (R : Finset ℕ)
    (φ : Fin H.k → Label n) (ho : (markedTrees H R φ).card=1)
    (a b : Fin H.k) (ha : representativeHit H a R φ) (hb : representativeHit H b R φ) : a=b := by
  obtain ⟨T,hT⟩ := Finset.card_eq_one.mp ho
  have hca := (treeHit_iff_mem_markedTrees H a R φ).mp ha.1
  have hcb := (treeHit_iff_mem_markedTrees H b R φ).mp hb.1
  rw [hT,Finset.mem_singleton] at hca hcb
  exact representative_same_tree H φ a b ha.2 hb.2 (hca.trans hcb.symm)

end WeldedPath.Supplement.BoundaryAdjustment

end

section

namespace WeldedPath.Supplement.BoundaryAdjustment

open Classical BoundaryCoefficients
open WeldedPath.WeightedCoefficients WeldedPath.HilbertSupport WeldedPath.CoefficientStability
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}

theorem markedTrees_card_le_outsideHits_add_one (H : AbsForest n) (a : Fin H.k)
    (R : Finset ℕ) (φ : Fin H.k → Label n) (hh : treeHit H a R φ) :
    (markedTrees H R φ).card ≤ outsideHits H a R φ+1 := by
  let U := Finset.univ.filter (fun u => u ∉ H.Ctree φ a ∧ (φ u).val ∈ R)
  have hsub : (markedTrees H R φ).erase (H.Ctree φ a) ⊆ U.image (fun u => H.Ctree φ u) := by
    intro T hT
    obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hT
    obtain ⟨u,hu,he⟩ := (mem_markedTrees H R φ T).mp hm
    refine Finset.mem_image.mpr ⟨u,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_,hu⟩,he⟩
    intro ht
    exact hne (he.symm.trans (ctree_eq_of_mem H φ u a ht).symm)
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_image_le)
  have he := Finset.card_erase_add_one ((treeHit_iff_mem_markedTrees H a R φ).mp hh)
  change _ ≤ outsideHits H a R φ at hcard
  omega

theorem representative_sum_pointwise (H : AbsForest n) (R : Finset ℕ)
    (φ : Fin H.k → Label n) (ho : (markedTrees H R φ).card ≠ 1)
    (v : Fin H.k → ℂ) (hv : ∀ a,v a ≠ 0 → representativeHit H a R φ) :
    ‖∑ a,v a‖^2 ≤ 2*∑ a,(outsideHits H a R φ : ℝ)*‖v a‖^2 := by
  by_cases hz : (markedTrees H R φ).card=0
  · have hzero : ∀ a,v a=0 := by
      intro a
      by_contra hn
      exact zero_marked_not_treeHit H a R φ hz (hv a hn).1
    simp only [hzero,Finset.sum_const_zero,norm_zero,zero_pow (by decide : 2 ≠ 0),mul_zero,le_refl]
  · let A := Finset.univ.filter (fun a => v a ≠ 0)
    have hcard : A.card ≤ (markedTrees H R φ).card := by
      apply Finset.card_le_card_of_injOn (fun a => H.Ctree φ a)
      · intro a ha
        exact (treeHit_iff_mem_markedTrees H a R φ).mp (hv a (Finset.mem_filter.mp ha).2).1
      · intro a ha b hb he
        exact representative_same_tree H φ a b (hv a (Finset.mem_filter.mp ha).2).2
          (hv b (Finset.mem_filter.mp hb).2).2 he
    have hsum : (∑ a,v a) = ∑ a ∈ A,v a := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro a _ ha
      by_contra hn
      exact ha (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn⟩)
    have hn : ‖∑ a ∈ A,v a‖ ≤ ∑ a ∈ A,‖v a‖ := norm_sum_le _ _
    have hsq := (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)).mpr hn
    calc
      _ = ‖∑ a ∈ A,v a‖^2 := congrArg (fun z : ℂ => ‖z‖^2) hsum
      _ ≤ (∑ a ∈ A,‖v a‖)^2 := hsq
      _ ≤ (A.card : ℝ)*∑ a ∈ A,‖v a‖^2 := sq_sum_le_card_mul_sum_sq
      _ ≤ ((markedTrees H R φ).card : ℝ)*∑ a,‖v a‖^2 := by
        apply mul_le_mul (by exact_mod_cast hcard) _
          (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun _ _ _ => sq_nonneg _)
      _ = ∑ a,((markedTrees H R φ).card : ℝ)*‖v a‖^2 := Finset.mul_sum _ _ _
      _ ≤ ∑ a,2*((outsideHits H a R φ : ℝ)*‖v a‖^2) := by
        apply Finset.sum_le_sum
        intro a _
        by_cases hza : v a=0
        · simp only [hza,norm_zero,zero_pow (by decide : 2 ≠ 0),mul_zero,le_refl]
        · have hc := markedTrees_card_le_outsideHits_add_one H a R φ (hv a hza).1
          have hc' : (markedTrees H R φ).card ≤ 2*outsideHits H a R φ := by omega
          have hr : ((markedTrees H R φ).card : ℝ) ≤ 2*(outsideHits H a R φ : ℝ) := by exact_mod_cast hc'
          nlinarith [mul_le_mul_of_nonneg_right hr (sq_nonneg ‖v a‖)]
      _ = _ := (Finset.mul_sum _ _ _).symm

theorem hitProjection_norm_sq_split (H : AbsForest n) (R : Finset ℕ) (j : ℕ)
    (f : Hil (Fin H.k → Label n)) :
    ‖f-hitProjection H R j f‖^2+‖hitProjection H R j f‖^2=‖f‖^2 := by
  simp only [EuclideanSpace.norm_sq_eq,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro φ _
  by_cases h : (markedTrees H R φ).card=j <;>
    simp only [PiLp.sub_apply,hitProjection,diagProj_apply,h,if_true,if_false,
      sub_self,sub_zero,norm_zero,zero_pow (by decide : 2 ≠ 0),zero_add,add_zero]

theorem representative_one_orthogonal (H : AbsForest n) (hH : H.IsValid)
    (B R : Finset ℕ) (v : Fin H.k → Hil (Fin H.k → Label n))
    (hv : ∀ a,v a ∈ representativeRootSpace l G H B R a) :
    ∀ a b,a ≠ b → inner ℂ (hitProjection H R 1 (v a)) (hitProjection H R 1 (v b))=0 := by
  intro a b hab
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  apply Finset.sum_eq_zero
  intro φ _
  change (hitProjection H R 1 (v b)) φ * star ((hitProjection H R 1 (v a)) φ)=0
  by_cases ho : (markedTrees H R φ).card=1
  · simp only [hitProjection,diagProj_apply,if_pos ho]
    by_cases ha : v a φ=0
    · rw [ha,star_zero,mul_zero]
    · have hb : v b φ=0 := by
        by_contra hb
        exact hab (representative_unique_at_one H R φ ho a b
          (representativeRootSpace_support H hH B R a _ (hv a) φ ha)
          (representativeRootSpace_support H hH B R b _ (hv b) φ hb))
      rw [hb,zero_mul]
  · simp only [hitProjection,diagProj_apply,if_neg ho,zero_mul]

theorem representative_family_error (H : AbsForest n) (hH : H.IsValid)
    (hc : ∀ v u,H.graph.Reachable v u)
    (hG : G.IsValid) (hn : 16 ≤ n) (hl : 2 ≤ l) (hln : l ≤ n-4)
    (B : Finset ℕ) (hB : Vbd n l ⊆ B) (hBw : Disjoint B (Vweld n))
    (hsmall : (H.k : ℝ)*(B.card : ℝ)*(4/(2:ℝ)^n) ≤ 1/2)
    (R : Finset ℕ) (hRw : Disjoint R (Vweld n))
    (v : Fin H.k → Hil (Fin H.k → Label n))
    (hv : ∀ a,v a ∈ representativeRootSpace l G H B R a) :
    ‖(∑ a,v a)-hitProjection H R 1 (∑ a,v a)‖^2 ≤
      (2*((H.k : ℝ)*8*(R.card : ℝ)/(2:ℝ)^n))*∑ a,‖v a‖^2 := by
  calc
    _ ≤ ∑ φ,2*∑ a,(outsideHits H a R φ : ℝ)*‖v a φ‖^2 := by
      rw [EuclideanSpace.norm_sq_eq]
      apply Finset.sum_le_sum
      intro φ _
      by_cases ho : (markedTrees H R φ).card=1
      · simp only [PiLp.sub_apply,hitProjection,diagProj_apply,if_pos ho,sub_self,norm_zero,
          zero_pow (by decide : 2 ≠ 0)]
        positivity
      · simp only [PiLp.sub_apply,hitProjection,diagProj_apply,if_neg ho,sub_zero,
          WithLp.ofLp_sum,Finset.sum_apply]
        exact representative_sum_pointwise H R φ ho (fun a => v a φ)
          (fun a hne => representativeRootSpace_support H hH B R a _ (hv a) φ hne)
    _ = 2*∑ a,∑ φ,(outsideHits H a R φ : ℝ)*‖v a φ‖^2 := by
      rw [← Finset.mul_sum,Finset.sum_comm]
    _ ≤ 2*∑ a,((H.k : ℝ)*8*(R.card : ℝ)/(2:ℝ)^n)*‖v a‖^2 := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Finset.sum_le_sum fun a _ => rootSourceSpace_outsideHits_energy_le H hH a (hc a)
        hG hn hl hln B hB hBw hsmall R hRw _
        (representativeRootSpace_le_rootSourceSpace H B R a (hv a))
    _ = _ := by rw [← Finset.mul_sum]; ring

theorem representative_family_survival (H : AbsForest n) (hH : H.IsValid)
    (hc : ∀ v u,H.graph.Reachable v u)
    (hG : G.IsValid) (hn : 16 ≤ n) (hl : 2 ≤ l) (hln : l ≤ n-4)
    (B : Finset ℕ) (hB : Vbd n l ⊆ B) (hBw : Disjoint B (Vweld n))
    (hsmall : (H.k : ℝ)*(B.card : ℝ)*(4/(2:ℝ)^n) ≤ 1/2)
    (R : Finset ℕ) (hRw : Disjoint R (Vweld n))
    (v : Fin H.k → Hil (Fin H.k → Label n))
    (hv : ∀ a,v a ∈ representativeRootSpace l G H B R a) :
    (1-((H.k : ℝ)*8*(R.card : ℝ)/(2:ℝ)^n))*∑ a,‖v a‖^2 ≤
      ‖hitProjection H R 1 (∑ a,v a)‖^2 := by
  rw [map_sum,norm_sum_sq_orthogonal _ (representative_one_orthogonal H hH B R v hv),Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  have he := markedRootSpace_one_error H hH a (hc a) hG hn hl hln B hB hBw hsmall R hRw
    (v a) (representativeRootSpace_le_markedRootSpace H hH B R a (hv a))
  have hs := hitProjection_norm_sq_split H R 1 (v a)
  nlinarith

/-- Coherent marked-root sums incur no factor for the number of roots. -/
theorem markedSpace_one_error (H : AbsForest n) (hH : H.IsValid)
    (hc : ∀ v u,H.graph.Reachable v u)
    (hG : G.IsValid) (hn : 16 ≤ n) (hl : 2 ≤ l) (hln : l ≤ n-4)
    (B : Finset ℕ) (hB : Vbd n l ⊆ B) (hBw : Disjoint B (Vweld n))
    (hsmall : (H.k : ℝ)*(B.card : ℝ)*(4/(2:ℝ)^n) ≤ 1/2)
    (R : Finset ℕ) (hRw : Disjoint R (Vweld n))
    (hloss : (H.k : ℝ)*8*(R.card : ℝ)/(2:ℝ)^n ≤ 1/2)
    (f : Hil (Fin H.k → Label n)) (hf : f ∈ markedSpace l G H B R) :
    ‖f-hitProjection H R 1 f‖^2 ≤ (4*((H.k : ℝ)*8*(R.card : ℝ)/(2:ℝ)^n))*‖f‖^2 := by
  obtain ⟨v,hv,he⟩ := markedSpace_representative_decomposition H hH hc B R f hf
  have hs := representative_family_survival H hH hc hG hn hl hln B hB hBw hsmall R hRw v hv
  have herr := representative_family_error H hH hc hG hn hl hln B hB hBw hsmall R hRw v hv
  rw [he] at hs herr
  have hsplit := hitProjection_norm_sq_split H R 1 f
  have hvnonneg : 0 ≤ ∑ a,‖v a‖^2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have heps : 0 ≤ (H.k : ℝ)*8*(R.card : ℝ)/(2:ℝ)^n := by positivity
  have hvle : ∑ a,‖v a‖^2 ≤ 2*‖f‖^2 := by
    nlinarith [sq_nonneg ‖f-hitProjection H R 1 f‖,
      mul_nonneg (sub_nonneg.mpr hloss) hvnonneg]
  calc
    _ ≤ (2*((H.k : ℝ)*8*(R.card : ℝ)/(2:ℝ)^n))*∑ a,‖v a‖^2 := herr
    _ ≤ (2*((H.k : ℝ)*8*(R.card : ℝ)/(2:ℝ)^n))*(2*‖f‖^2) :=
      mul_le_mul_of_nonneg_left hvle (by positivity)
    _ = _ := by ring

end WeldedPath.Supplement.BoundaryAdjustment


end

section

namespace WeldedPath.Supplement.BoundaryAdjustment

open Classical AllBoundaryStability
open WeldedPath.WeightedCoefficients WeldedPath.HilbertSupport
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}

private theorem norm_add_sq_bound {E : Type*} [NormedAddCommGroup E] (x y : E) :
    ‖x+y‖^2 ≤ 2*(‖x‖^2+‖y‖^2) := by
  have h := norm_add_le x y
  have hx := norm_nonneg x
  have hy := norm_nonneg y
  have hxy := norm_nonneg (x+y)
  nlinarith [sq_nonneg (‖x‖-‖y‖)]

section Actual

variable (H : AbsForest n) (hH : H.IsValid) (hc : ∀ v u,H.graph.Reachable v u)
    (hG : G.IsValid) (hn : 16 ≤ n) (hl : 2 ≤ l) (hln : l ≤ n-4)
    (B : Finset ℕ) (hB : Vbd n l ⊆ B) (hBw : Disjoint B (Vweld n))
    (hsmall : (H.k : ℝ)*(B.card : ℝ)*(4/(2:ℝ)^n) ≤ 1/2)
    (R : Finset ℕ) (hRw : Disjoint R (Vweld n))
    (hloss : (H.k : ℝ)*8*(R.card : ℝ)/(2:ℝ)^n ≤ 1/8)

include hH hc hG hn hl hln hB hBw hsmall hRw hloss

theorem connected_boundary_forward (f : Hil (Fin H.k → Label n))
    (hf : f ∈ allSectorSpace l G H B) :
    ∃ w ∈ allSectorSpace l G H (B ∪ R),
      ‖f-w‖^2 ≤ (8*((H.k : ℝ)*8*(R.card : ℝ)/(2:ℝ)^n))*‖f‖^2 := by
  let K := markedSpace l G H B R
  let h := K.starProjection f
  let g := f-h
  have hh : h ∈ K := K.starProjection_apply_mem f
  have hg : g ∈ allSectorSpace l G H B :=
    (allSectorSpace l G H B).sub_mem hf (markedSpace_le_allSectorSpace H hH B R hc hh)
  have hgo : g ∈ Kᗮ := K.sub_starProjection_mem_orthogonal f
  have horth : inner ℂ h g=0 := (K.mem_orthogonal g).mp hgo h hh
  have heq : h+g=f := by dsimp [g]; abel
  have he := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero h g horth
  rw [heq] at he
  have hgerr := marked_complement_zero_error H hH hc hG hn hl hln B hB hBw hsmall R hRw g hg hgo
  have hherr := markedSpace_one_error H hH hc hG hn hl hln B hB hBw hsmall R hRw (by linarith) h hh
  refine ⟨hitProjection H R 0 g+hitProjection H R 1 h,?_,?_⟩
  · rw [allSectorSpace_union_decomposition H hH B R hc]
    exact Submodule.add_mem_sup ⟨g,hg,rfl⟩ ⟨h,hh,rfl⟩
  · have hid : f-(hitProjection H R 0 g+hitProjection H R 1 h)=
        (g-hitProjection H R 0 g)+(h-hitProjection H R 1 h) := by
      rw [← heq]; abel
    rw [hid]
    have hb := norm_add_sq_bound (g-hitProjection H R 0 g) (h-hitProjection H R 1 h)
    have heps : 0 ≤ (H.k : ℝ)*8*(R.card : ℝ)/(2:ℝ)^n := by positivity
    nlinarith [mul_nonneg heps (sq_nonneg ‖g‖)]

set_option maxHeartbeats 1000000 in
theorem connected_boundary_reverse (w : Hil (Fin H.k → Label n))
    (hw : w ∈ allSectorSpace l G H (B ∪ R)) :
    ∃ f ∈ allSectorSpace l G H B,
      ‖w-f‖^2 ≤ (16*((H.k : ℝ)*8*(R.card : ℝ)/(2:ℝ)^n))*‖w‖^2 := by
  rw [allSectorSpace_union_decomposition H hH B R hc] at hw
  obtain ⟨x,hx,y,hy,hxy⟩ := Submodule.mem_sup.mp hw
  obtain ⟨f,hf,hfx⟩ := hx
  obtain ⟨h,hh,hhy⟩ := hy
  change hitProjection H R 0 f=x at hfx
  change hitProjection H R 1 h=y at hhy
  let K := markedSpace l G H B R
  let g := f-K.starProjection f
  have hg : g ∈ allSectorSpace l G H B := (allSectorSpace l G H B).sub_mem hf
    (markedSpace_le_allSectorSpace H hH B R hc (K.starProjection_apply_mem f))
  have hgo : g ∈ Kᗮ := K.sub_starProjection_mem_orthogonal f
  have hgx : hitProjection H R 0 g=x := by
    dsimp only [g]
    rw [map_sub,hitProjection_zero_markedSpace H B R _ (K.starProjection_apply_mem f),sub_zero,hfx]
  have hgerr := marked_complement_zero_error H hH hc hG hn hl hln B hB hBw hsmall R hRw g hg hgo
  have hherr := markedSpace_one_error H hH hc hG hn hl hln B hB hBw hsmall R hRw (by linarith) h hh
  have hgsplit := hitProjection_norm_sq_split H R 0 g
  have hhsplit := hitProjection_norm_sq_split H R 1 h
  rw [hgx] at hgerr hgsplit
  rw [hhy] at hherr hhsplit
  have hgsmall : ‖g‖^2 ≤ 2*‖x‖^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr (show (H.k : ℝ)*8*(R.card : ℝ)/(2:ℝ)^n ≤ 1/2 by linarith)) (sq_nonneg ‖g‖)]
  have hhsmall : ‖h‖^2 ≤ 2*‖y‖^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr (show 4*((H.k : ℝ)*8*(R.card : ℝ)/(2:ℝ)^n) ≤ 1/2 by linarith)) (sq_nonneg ‖h‖)]
  have ho : inner ℂ x y=0 := by
    have hxort := decomposition_summands_orthogonal (l:=l) (G:=G) H B R ⟨f,hf,hfx⟩
    exact (Submodule.mem_orthogonal' _ _).mp hxort y ⟨h,hh,hhy⟩
  have hwenergy := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero x y ho
  rw [hxy] at hwenergy
  refine ⟨g+h,(allSectorSpace l G H B).add_mem hg
    (markedSpace_le_allSectorSpace H hH B R hc hh),?_⟩
  have hid : w-(g+h)=(x-g)+(y-h) := by rw [← hxy]; abel
  rw [hid]
  have hb := norm_add_sq_bound (x-g) (y-h)
  rw [norm_sub_rev x g,norm_sub_rev y h] at hb
  have heps : 0 ≤ (H.k : ℝ)*8*(R.card : ℝ)/(2:ℝ)^n := by positivity
  have hsum : ‖g‖^2+‖h‖^2 ≤ 2*‖w‖^2 := by linarith
  calc
    _ ≤ 2*(‖g-x‖^2+‖h-y‖^2) := by
      simpa only [norm_sub_rev] using hb
    _ ≤ 2*((((H.k : ℝ)*8*(R.card : ℝ)/(2:ℝ)^n))*‖g‖^2+
        (4*((H.k : ℝ)*8*(R.card : ℝ)/(2:ℝ)^n))*‖h‖^2) := by
      exact mul_le_mul_of_nonneg_left (add_le_add hgerr hherr) (by norm_num)
    _ ≤ (8*((H.k : ℝ)*8*(R.card : ℝ)/(2:ℝ)^n))*(‖g‖^2+‖h‖^2) := by
      nlinarith [mul_nonneg heps (sq_nonneg ‖g‖)]
    _ ≤ (8*((H.k : ℝ)*8*(R.card : ℝ)/(2:ℝ)^n))*(2*‖w‖^2) :=
      mul_le_mul_of_nonneg_left hsum (mul_nonneg (by norm_num) heps)
    _ = _ := by ring

end Actual

section Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]



end Geometry


end WeldedPath.Supplement.BoundaryAdjustment


end

section

namespace WeldedPath.Supplement.BoundaryAdjustment

open Classical ComponentForest EdgePotential
open WeldedPath.ProductDecomposition
open scoped BigOperators

variable {n : ℕ}

private theorem projection_distance_sq_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (T : Submodule ℂ E) (f g : E) (hg : g ∈ T) :
    ‖f-T.starProjection f‖^2 ≤ ‖f-g‖^2 := by
  have hz : Tᗮ.starProjection g=0 := T.starProjection_orthogonal_apply_eq_zero hg
  have he : f-T.starProjection f=Tᗮ.starProjection (f-g) := by
    rw [map_sub,hz,sub_zero,Submodule.starProjection_orthogonal']
    rfl
  rw [he]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (Tᗮ.norm_starProjection_apply_le _)

theorem component_projection_error (H : AbsForest n) (a : Roots H)
    (S : (r : Roots H) → Submodule ℂ (Hil (LocalAssignment H r)))
    (T : Submodule ℂ (Hil (LocalAssignment H a))) (c : ℝ)
    (happ : ∀ f ∈ S a,∃ g ∈ T,‖f-g‖^2 ≤ c*‖f‖^2)
    (f : Hil (Fin H.k → Label n)) (hf : f ∈ productSpace H S) :
    ‖f-componentOperator H a T.starProjection.toLinearMap f‖^2 ≤ c*‖f‖^2 := by
  have hf' := (regroupOne_mem_iff H S a f).mpr hf
  rw [← (regroupOneHil H a).norm_map (f-componentOperator H a T.starProjection.toLinearMap f),norm_columns]
  calc
    _ ≤ ∑ y : OneSpectator H a,c*‖column (regroupOneHil H a f) y‖^2 := by
      apply Finset.sum_le_sum
      intro y _
      have hc := ((mem_tensorSpace _ _ _).mp hf').1 y
      obtain ⟨g,hg,herr⟩ := happ _ hc
      have he : column (regroupOneHil H a (f-componentOperator H a T.starProjection.toLinearMap f)) y =
          column (regroupOneHil H a f) y-T.starProjection (column (regroupOneHil H a f) y) := by
        rw [map_sub]
        have hm := componentOperator_column H a T.starProjection.toLinearMap f y
        change column (regroupOneHil H a f) y-
          column (regroupOneHil H a (componentOperator H a T.starProjection.toLinearMap f)) y = _
        rw [hm]
        rfl
      rw [he]
      exact (projection_distance_sq_le T _ g hg).trans herr
    _ = c*‖f‖^2 := by rw [← Finset.mul_sum,← norm_columns,(regroupOneHil H a).norm_map]

theorem component_projection_residual_orthogonal (H : AbsForest n) (a : Roots H)
    (T : Submodule ℂ (Hil (LocalAssignment H a)))
    (S : (r : Roots H) → Submodule ℂ (Hil (LocalAssignment H r))) (hS : S a ≤ T)
    (f g : Hil (Fin H.k → Label n)) (hg : g ∈ productSpace H S) :
    inner ℂ (f-componentOperator H a T.starProjection.toLinearMap f) g=0 := by
  have hg' := (regroupOne_mem_iff H S a g).mpr hg
  rw [← (regroupOneHil H a).inner_map_map,inner_columns]
  apply Finset.sum_eq_zero
  intro y _
  have hm := componentOperator_column H a T.starProjection.toLinearMap f y
  have he : column (regroupOneHil H a (f-componentOperator H a T.starProjection.toLinearMap f)) y =
      column (regroupOneHil H a f) y-T.starProjection (column (regroupOneHil H a f) y) := by
    rw [map_sub]
    change column (regroupOneHil H a f) y-
      column (regroupOneHil H a (componentOperator H a T.starProjection.toLinearMap f)) y = _
    rw [hm]
    rfl
  rw [he]
  exact (T.mem_orthogonal' _).mp (T.sub_starProjection_mem_orthogonal _)
    _ (hS (((mem_tensorSpace _ _ _).mp hg').1 y))

/-- Component changes accumulate squared errors. This statement allows
arbitrary coherent combinations of the product generators. -/
theorem productSpace_approximation_finset (H : AbsForest n)
    (T : (r : Roots H) → Submodule ℂ (Hil (LocalAssignment H r)))
    (c : Roots H → ℝ) (hc : ∀ r,0 ≤ c r) (D : Finset (Roots H))
    (S : (r : Roots H) → Submodule ℂ (Hil (LocalAssignment H r)))
    (happ : ∀ r ∈ D,∀ f ∈ S r,∃ g ∈ T r,‖f-g‖^2 ≤ c r*‖f‖^2)
    (f : Hil (Fin H.k → Label n)) (hf : f ∈ productSpace H S) :
    ∃ g ∈ productSpace H (fun r => if r ∈ D then T r else S r),
      ‖f-g‖^2 ≤ (∑ r ∈ D,c r)*‖f‖^2 := by
  induction D using Finset.induction_on generalizing S f with
  | empty =>
      refine ⟨f,?_,?_⟩
      · simpa using hf
      · simp only [sub_self,norm_zero,zero_pow (by decide : 2 ≠ 0),Finset.sum_empty,zero_mul,le_refl]
  | @insert a D ha ih =>
      let S' := Function.update S a (T a)
      let f' := componentOperator H a (T a).starProjection.toLinearMap f
      have hf' : f' ∈ productSpace H S' := by
        apply componentOperator_mem_productSpace H a S S' (T a).starProjection.toLinearMap
        · intro z _
          change (T a).starProjection z ∈ S' a
          rw [show S' a=T a from Function.update_self _ _ _]
          exact (T a).starProjection_apply_mem z
        · intro r hr
          simp only [S',Function.update_of_ne hr,le_refl]
        · exact hf
      have hlocal : ∀ r ∈ D,∀ z ∈ S' r,∃ w ∈ T r,‖z-w‖^2 ≤ c r*‖z‖^2 := by
        intro r hr z hz
        have hra : r ≠ a := fun he => ha (he ▸ hr)
        rw [show S' r=S r from Function.update_of_ne hra _ _] at hz
        exact happ r (Finset.mem_insert_of_mem hr) z hz
      obtain ⟨g,hg,herr⟩ := ih S' hlocal f' hf'
      have hU : (fun r => if r ∈ D then T r else S' r)=
          (fun r => if r ∈ insert a D then T r else S r) := by
        funext r
        by_cases hra : r=a
        · subst r
          simp only [ha,if_false,S',Function.update_self,Finset.mem_insert_self,if_true]
        · simp only [S',Function.update_of_ne hra,Finset.mem_insert,hra,false_or]
      have hUa : (if a ∈ D then T a else S' a) ≤ T a := by
        simp only [ha,if_false,S',Function.update_self,le_refl]
      have hfa : S' a ≤ T a := by simp only [S',Function.update_self,le_refl]
      have horth0 := component_projection_residual_orthogonal H a (T a) S' hfa f f' hf'
      have horth1 := component_projection_residual_orthogonal H a (T a)
        (fun r => if r ∈ D then T r else S' r) hUa f g hg
      have horth : inner ℂ (f-f') (f'-g)=0 := by
        rw [inner_sub_right,horth0,horth1,sub_self]
      have hnorm := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (f-f') f' horth0
      rw [sub_add_cancel] at hnorm
      have hcontract : ‖f'‖^2 ≤ ‖f‖^2 := by nlinarith [sq_nonneg ‖f-f'‖]
      have hfirst := component_projection_error H a S (T a) (c a)
        (happ a (Finset.mem_insert_self _ _)) f hf
      have he := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (f-f') (f'-g) horth
      rw [sub_add_sub_cancel] at he
      have he' : ‖f-g‖^2=‖f-f'‖^2+‖f'-g‖^2 := by simpa only [pow_two] using he
      refine ⟨g,hU ▸ hg,?_⟩
      rw [he',Finset.sum_insert ha,add_mul]
      apply add_le_add hfirst
      exact herr.trans (mul_le_mul_of_nonneg_left hcontract (Finset.sum_nonneg fun r _ => hc r))

theorem productSpace_approximation (H : AbsForest n)
    (S T : (r : Roots H) → Submodule ℂ (Hil (LocalAssignment H r)))
    (c : Roots H → ℝ) (hc : ∀ r,0 ≤ c r)
    (happ : ∀ r,∀ f ∈ S r,∃ g ∈ T r,‖f-g‖^2 ≤ c r*‖f‖^2)
    (f : Hil (Fin H.k → Label n)) (hf : f ∈ productSpace H S) :
    ∃ g ∈ productSpace H T,‖f-g‖^2 ≤ (∑ r,c r)*‖f‖^2 := by
  simpa only [Finset.mem_univ,if_true] using
    productSpace_approximation_finset H T c hc Finset.univ S (fun r _ => happ r) f hf

end WeldedPath.Supplement.BoundaryAdjustment


end

section

namespace WeldedPath.Supplement.BoundaryAdjustment

open Classical ComponentForest DisconnectedStability AllBoundaryStability
open scoped BigOperators

variable {n l : ℕ} {G : WeldedInstance n}

theorem component_marked_budget (H : AbsForest n) (R : Finset ℕ) (r : Roots H) :
    ((componentForest H r.val).k : ℝ)*8*(R.card : ℝ)/(2:ℝ)^n ≤
      (H.k : ℝ)*8*(R.card : ℝ)/(2:ℝ)^n := by
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (by norm_num)
  exact_mod_cast component_k_le H r.val

theorem sum_component_marked_budget (H : AbsForest n) (R : Finset ℕ) (c : ℝ) :
    (∑ r : Roots H,c*(((componentForest H r.val).k : ℝ)*8*(R.card : ℝ)/(2:ℝ)^n)) =
      c*((H.k : ℝ)*8*(R.card : ℝ)/(2:ℝ)^n) := by
  have hk : (∑ r : Roots H,((componentForest H r.val).k : ℝ))=(H.k : ℝ) := by
    exact_mod_cast sum_component_card H
  calc
    _ = (∑ r : Roots H,((componentForest H r.val).k : ℝ))*(c*8*(R.card : ℝ)/(2:ℝ)^n) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro r _
      ring
    _ = _ := by rw [hk]; ring

section Actual

variable (H : AbsForest n) (hH : H.IsValid)
    (hG : G.IsValid) (hn : 16 ≤ n) (hl : 2 ≤ l) (hln : l ≤ n-4)
    (B : Finset ℕ) (hB : Vbd n l ⊆ B) (hBw : Disjoint B (Vweld n))
    (hsmall : (H.k : ℝ)*(B.card : ℝ)*(4/(2:ℝ)^n) ≤ 1/2)
    (R : Finset ℕ) (hRw : Disjoint R (Vweld n))
    (hloss : (H.k : ℝ)*8*(R.card : ℝ)/(2:ℝ)^n ≤ 1/8)

include hH hG hn hl hln hB hBw hsmall hRw hloss

theorem global_boundary_forward (f : Hil (Fin H.k → Label n))
    (hf : f ∈ coefficientSpace l G H B) :
    ∃ w ∈ coefficientSpace l G H (B ∪ R),
      ‖f-w‖^2 ≤ (8*((H.k : ℝ)*8*(R.card : ℝ)/(2:ℝ)^n))*‖f‖^2 := by
  have hlocal (r : Roots H) : ∀ f ∈ componentSpaces l G H B r,
      ∃ w ∈ componentSpaces l G H (B ∪ R) r,
        ‖f-w‖^2 ≤ (8*(((componentForest H r.val).k : ℝ)*8*(R.card : ℝ)/(2:ℝ)^n))*‖f‖^2 := by
    exact connected_boundary_forward (componentForest H r.val) (component_valid H hH r.val)
      (component_connected H r.val) hG hn hl hln B hB hBw
      (component_survival_budget H B hsmall r) R hRw
      ((component_marked_budget H R r).trans hloss)
  obtain ⟨w,hw,herr⟩ := productSpace_approximation H (componentSpaces l G H B)
    (componentSpaces l G H (B ∪ R))
    (fun r => 8*(((componentForest H r.val).k : ℝ)*8*(R.card : ℝ)/(2:ℝ)^n))
    (fun _ => by positivity) hlocal f hf
  rw [sum_component_marked_budget H R 8] at herr
  exact ⟨w,hw,herr⟩

theorem global_boundary_reverse (w : Hil (Fin H.k → Label n))
    (hw : w ∈ coefficientSpace l G H (B ∪ R)) :
    ∃ f ∈ coefficientSpace l G H B,
      ‖w-f‖^2 ≤ (16*((H.k : ℝ)*8*(R.card : ℝ)/(2:ℝ)^n))*‖w‖^2 := by
  have hlocal (r : Roots H) : ∀ w ∈ componentSpaces l G H (B ∪ R) r,
      ∃ f ∈ componentSpaces l G H B r,
        ‖w-f‖^2 ≤ (16*(((componentForest H r.val).k : ℝ)*8*(R.card : ℝ)/(2:ℝ)^n))*‖w‖^2 := by
    exact connected_boundary_reverse (componentForest H r.val) (component_valid H hH r.val)
      (component_connected H r.val) hG hn hl hln B hB hBw
      (component_survival_budget H B hsmall r) R hRw
      ((component_marked_budget H R r).trans hloss)
  obtain ⟨f,hf,herr⟩ := productSpace_approximation H (componentSpaces l G H (B ∪ R))
    (componentSpaces l G H B)
    (fun r => 16*(((componentForest H r.val).k : ℝ)*8*(R.card : ℝ)/(2:ℝ)^n))
    (fun _ => by positivity) hlocal w hw
  rw [sum_component_marked_budget H R 16] at herr
  exact ⟨f,hf,herr⟩


end Actual
end WeldedPath.Supplement.BoundaryAdjustment


end

section

namespace WeldedPath.Supplement.BoundaryAdjustment

open Classical DisconnectedStability DescriptionCoefficients

theorem boundary_coefficient_comparison {n l : ℕ} {G : WeldedInstance n}
    (H : AbsForest n) (hH : H.IsValid) (hG : G.IsValid)
    (hn : 16 ≤ n) (hl : 2 ≤ l) (hln : l ≤ n-4)
    (B : Finset ℕ) (hB : Vbd n l ⊆ B) (hBw : Disjoint B (Vweld n))
    (hsmall : (H.k : ℝ)*(B.card : ℝ)*(4/(2:ℝ)^n) ≤ 1/2)
    (R : Finset ℕ) (hRw : Disjoint R (Vweld n))
    (hloss : (H.k : ℝ)*8*(R.card : ℝ)/(2:ℝ)^n ≤ 1/8) :
    let S := fun (A : Finset ℕ) => Submodule.span ℂ
      {f : Hil (Fin H.k → Label n) | ∃ (sel : Finset (Fin H.k)) (φ₀ : Fin H.k → Label n),
        (Description.mk H sel φ₀).IsValid ∧ f = WithLp.toLp 2 (fun φ : Fin H.k → Label n =>
          ((Real.sqrt (if (∀ s ∈ sel,H.Wfix φ s = H.Wfix φ₀ s) ∧
            (∀ s ∈ sel, ∀ u, H.graph.Reachable s u → u ∉ H.Ctree φ s → (φ u).val ∉ A)
            then H.muRef l G φ else 0)) : ℂ))}
    (∀ f ∈ S B, ∃ g ∈ S (B ∪ R), ‖f-g‖^2 ≤ (8*((H.k:ℝ)*8*(R.card:ℝ)/(2:ℝ)^n))*‖f‖^2) ∧
    (∀ g ∈ S (B ∪ R), ∃ f ∈ S B, ‖g-f‖^2 ≤ (16*((H.k:ℝ)*8*(R.card:ℝ)/(2:ℝ)^n))*‖g‖^2) := by
  change (∀ f ∈ descriptionSpan l G H B, ∃ g ∈ descriptionSpan l G H (B ∪ R), _) ∧
    (∀ g ∈ descriptionSpan l G H (B ∪ R), ∃ f ∈ descriptionSpan l G H B, _)
  rw [← coefficientSpace_eq_descriptionSpan l G H hH B,← coefficientSpace_eq_descriptionSpan l G H hH (B ∪ R)]
  exact ⟨global_boundary_forward H hH hG hn hl hln B hB hBw hsmall R hRw hloss,
    global_boundary_reverse H hH hG hn hl hln B hB hBw hsmall R hRw hloss⟩

end WeldedPath.Supplement.BoundaryAdjustment

end

open Classical WeldedPath WeldedPath.Supplement

theorem solution {n l : ℕ} {G : WeldedInstance n}
    (H : AbsForest n) (hH : H.IsValid) (hG : G.IsValid)
    (hn : 16 ≤ n) (hl : 2 ≤ l) (hln : l ≤ n-4)
    (B : Finset ℕ) (hB : Vbd n l ⊆ B) (hBw : Disjoint B (Vweld n))
    (hsmall : (H.k : ℝ)*(B.card : ℝ)*(4/(2:ℝ)^n) ≤ 1/2)
    (R : Finset ℕ) (hRw : Disjoint R (Vweld n))
    (hloss : (H.k : ℝ)*8*(R.card : ℝ)/(2:ℝ)^n ≤ 1/8) :
    let S := fun (A : Finset ℕ) => Submodule.span ℂ
      {f : Hil (Fin H.k → Label n) | ∃ (sel : Finset (Fin H.k)) (φ₀ : Fin H.k → Label n),
        (Description.mk H sel φ₀).IsValid ∧ f = WithLp.toLp 2 (fun φ : Fin H.k → Label n =>
          ((Real.sqrt (if (∀ s ∈ sel,H.Wfix φ s = H.Wfix φ₀ s) ∧
            (∀ s ∈ sel, ∀ u, H.graph.Reachable s u → u ∉ H.Ctree φ s → (φ u).val ∉ A)
            then H.muRef l G φ else 0)) : ℂ))}
    (∀ f ∈ S B, ∃ g ∈ S (B ∪ R), ‖f-g‖^2 ≤ (8*((H.k:ℝ)*8*(R.card:ℝ)/(2:ℝ)^n))*‖f‖^2) ∧
    (∀ g ∈ S (B ∪ R), ∃ f ∈ S B, ‖g-f‖^2 ≤ (16*((H.k:ℝ)*8*(R.card:ℝ)/(2:ℝ)^n))*‖g‖^2) := by
  exact BoundaryAdjustment.boundary_coefficient_comparison H hH hG hn hl hln B hB hBw hsmall R hRw hloss
