-- Prove2me | solution 1 for PathsTreesFlowers.Duality.lemma_4_2
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-28T08:06:13.613307+00:00
-- url     : https://prove2.me/submissions/071a0746-b358-49e7-ad37-049c4318fac0

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Sym.Sym2
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_PathsTreesFlowers_Duality_Basic

namespace SolPathsTreesFlowersLemma42

set_option linter.unusedSectionVars false

open EdmondsMatching65.Polyhedron (IsMatching)
open PathsTreesFlowers.Duality (AltTree IsMaxMatchingOn)

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-! ### Part 1: Endpoint helpers for `AltTree` -/

lemma not_mem_outer_of_mem_inner {G : EdmondsMatching65.Polyhedron.Graph V E} (J : AltTree G) {u : V} (hu : u ∈ J.inner) :
    u ∉ J.outer :=
  Finset.disjoint_left.mp J.disjoint hu

lemma not_mem_inner_of_mem_outer {G : EdmondsMatching65.Polyhedron.Graph V E} (J : AltTree G) {w : V} (hw : w ∈ J.outer) :
    w ∉ J.inner :=
  Finset.disjoint_right.mp J.disjoint hw

lemma ne_of_mem_inner_of_mem_outer {G : EdmondsMatching65.Polyhedron.Graph V E} (J : AltTree G) {u w : V}
    (hu : u ∈ J.inner) (hw : w ∈ J.outer) : u ≠ w :=
  fun h => not_mem_outer_of_mem_inner J hu (h ▸ hw)

lemma filter_inner_ends_eq {G : EdmondsMatching65.Polyhedron.Graph V E} (J : AltTree G) {e : E} {u w : V}
    (hends : G.ends e = s(u, w)) (hu : u ∈ J.inner) (hw : w ∈ J.outer) :
    J.inner.filter (fun x => x ∈ G.ends e) = {u} := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_singleton, hends, Sym2.mem_iff]
  constructor
  · rintro ⟨hx, rfl | rfl⟩
    · rfl
    · exact False.elim (not_mem_inner_of_mem_outer J hw hx)
  · rintro rfl
    exact ⟨hu, Or.inl rfl⟩

lemma filter_outer_ends_eq {G : EdmondsMatching65.Polyhedron.Graph V E} (J : AltTree G) {e : E} {u w : V}
    (hends : G.ends e = s(u, w)) (hu : u ∈ J.inner) (hw : w ∈ J.outer) :
    J.outer.filter (fun x => x ∈ G.ends e) = {w} := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_singleton, hends, Sym2.mem_iff]
  constructor
  · rintro ⟨hx, rfl | rfl⟩
    · exact False.elim (not_mem_outer_of_mem_inner J hu hx)
    · rfl
  · rintro rfl
    exact ⟨hw, Or.inr rfl⟩

lemma card_filter_inner_ends {G : EdmondsMatching65.Polyhedron.Graph V E} (J : AltTree G) {e : E} (he : e ∈ J.edges) :
    (J.inner.filter (fun x => x ∈ G.ends e)).card = 1 := by
  obtain ⟨u, hu, w, hw, hends⟩ := J.edge_ends e he
  rw [filter_inner_ends_eq J hends hu hw, Finset.card_singleton]

lemma card_filter_outer_ends {G : EdmondsMatching65.Polyhedron.Graph V E} (J : AltTree G) {e : E} (he : e ∈ J.edges) :
    (J.outer.filter (fun x => x ∈ G.ends e)).card = 1 := by
  obtain ⟨u, hu, w, hw, hends⟩ := J.edge_ends e he
  rw [filter_outer_ends_eq J hends hu hw, Finset.card_singleton]

/-! ### Part 2: Double counting and `J.outer.card = J.inner.card + 1` -/

lemma sum_card_filter_ends (G : EdmondsMatching65.Polyhedron.Graph V E) (S : Finset V) (F : Finset E) :
    ∑ v ∈ S, (F.filter (fun e => v ∈ G.ends e)).card =
      ∑ e ∈ F, (S.filter (fun v => v ∈ G.ends e)).card := by
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Finset.sum_comm

lemma edges_card_eq_two_mul_inner {G : EdmondsMatching65.Polyhedron.Graph V E} (J : AltTree G) :
    J.edges.card = 2 * J.inner.card := by
  have h1 : ∑ u ∈ J.inner, (J.edges.filter (fun e => u ∈ G.ends e)).card = 2 * J.inner.card := by
    calc ∑ u ∈ J.inner, (J.edges.filter (fun e => u ∈ G.ends e)).card
        = ∑ _u ∈ J.inner, 2 := Finset.sum_congr rfl fun u hu => J.inner_deg u hu
      _ = 2 * J.inner.card := by simp [Nat.mul_comm]
  have h2 : ∑ e ∈ J.edges, (J.inner.filter (fun u => u ∈ G.ends e)).card = J.edges.card := by
    calc ∑ e ∈ J.edges, (J.inner.filter (fun u => u ∈ G.ends e)).card
        = ∑ _e ∈ J.edges, 1 := Finset.sum_congr rfl fun e he => card_filter_inner_ends J he
      _ = J.edges.card := by simp
  linarith [sum_card_filter_ends G J.inner J.edges]

lemma sum_outer_deg_eq_edges_card {G : EdmondsMatching65.Polyhedron.Graph V E} (J : AltTree G) :
    ∑ w ∈ J.outer, (J.edges.filter (fun e => w ∈ G.ends e)).card = J.edges.card := by
  calc ∑ w ∈ J.outer, (J.edges.filter (fun e => w ∈ G.ends e)).card
      = ∑ e ∈ J.edges, (J.outer.filter (fun w => w ∈ G.ends e)).card :=
        sum_card_filter_ends G J.outer J.edges
    _ = ∑ _e ∈ J.edges, 1 := Finset.sum_congr rfl fun e he => card_filter_outer_ends J he
    _ = J.edges.card := by simp

lemma outer_card_eq_inner_card_add_one {G : EdmondsMatching65.Polyhedron.Graph V E} (J : AltTree G) :
    J.outer.card = J.inner.card + 1 := by
  have hverts : (J.inner ∪ J.outer).card = J.inner.card + J.outer.card :=
    Finset.card_union_of_disjoint J.disjoint
  have hcard := J.card_verts
  have hedges := edges_card_eq_two_mul_inner J
  omega

/-! ### Part 3: Matchings in `J.edges` and exposed vertex counting -/

lemma card_filter_matching_eq_ite {G : EdmondsMatching65.Polyhedron.Graph V E} {M : Finset E} (hM : IsMatching G M) (x : V) :
    (M.filter (fun e => x ∈ G.ends e)).card = if PathsTreesFlowers.Duality.IsExposed G M x then 0 else 1 := by
  split_ifs with hexp
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    exact hexp
  · simp only [PathsTreesFlowers.Duality.IsExposed, not_forall, not_not] at hexp
    rcases hexp with ⟨e, he, hxe⟩
    have hle : (M.filter (fun e => x ∈ G.ends e)).card ≤ 1 := by
      refine Finset.card_le_one.mpr ?_
      intro e₁ he₁ e₂ he₂
      simp only [Finset.mem_filter] at he₁ he₂
      by_contra hne
      exact hM e₁ he₁.1 e₂ he₂.1 hne x he₁.2 he₂.2
    have hge : 1 ≤ (M.filter (fun e => x ∈ G.ends e)).card :=
      Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨he, hxe⟩⟩
    omega

lemma card_filter_not_exposed_eq_sum {G : EdmondsMatching65.Polyhedron.Graph V E} {M : Finset E} (hM : IsMatching G M)
    (S : Finset V) :
    (S.filter (fun x => ¬ PathsTreesFlowers.Duality.IsExposed G M x)).card =
      ∑ x ∈ S, (M.filter (fun e => x ∈ G.ends e)).card := by
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [card_filter_matching_eq_ite hM x]
  split_ifs <;> rfl

lemma inner_exposed_add_matching_card {G : EdmondsMatching65.Polyhedron.Graph V E} (J : AltTree G) {M : Finset E}
    (hM_sub : M ⊆ J.edges) (hM : IsMatching G M) :
    (J.inner.filter (PathsTreesFlowers.Duality.IsExposed G M)).card + M.card = J.inner.card := by
  have hsum : ∑ u ∈ J.inner, (M.filter (fun e => u ∈ G.ends e)).card = M.card := by
    calc ∑ u ∈ J.inner, (M.filter (fun e => u ∈ G.ends e)).card
        = ∑ e ∈ M, (J.inner.filter (fun u => u ∈ G.ends e)).card :=
          sum_card_filter_ends G J.inner M
      _ = ∑ _e ∈ M, 1 := Finset.sum_congr rfl fun e he => card_filter_inner_ends J (hM_sub he)
      _ = M.card := by simp
  have hpart := Finset.card_filter_add_card_filter_not (s := J.inner) (p := PathsTreesFlowers.Duality.IsExposed G M)
  rw [card_filter_not_exposed_eq_sum hM J.inner, hsum] at hpart
  exact hpart

lemma outer_exposed_add_matching_card {G : EdmondsMatching65.Polyhedron.Graph V E} (J : AltTree G) {M : Finset E}
    (hM_sub : M ⊆ J.edges) (hM : IsMatching G M) :
    (J.outer.filter (PathsTreesFlowers.Duality.IsExposed G M)).card + M.card = J.outer.card := by
  have hsum : ∑ w ∈ J.outer, (M.filter (fun e => w ∈ G.ends e)).card = M.card := by
    calc ∑ w ∈ J.outer, (M.filter (fun e => w ∈ G.ends e)).card
        = ∑ e ∈ M, (J.outer.filter (fun w => w ∈ G.ends e)).card :=
          sum_card_filter_ends G J.outer M
      _ = ∑ _e ∈ M, 1 := Finset.sum_congr rfl fun e he => card_filter_outer_ends J (hM_sub he)
      _ = M.card := by simp
  have hpart := Finset.card_filter_add_card_filter_not (s := J.outer) (p := PathsTreesFlowers.Duality.IsExposed G M)
  rw [card_filter_not_exposed_eq_sum hM J.outer, hsum] at hpart
  exact hpart

lemma matching_card_le_inner_card {G : EdmondsMatching65.Polyhedron.Graph V E} (J : AltTree G) {M : Finset E}
    (hM_sub : M ⊆ J.edges) (hM : IsMatching G M) :
    M.card ≤ J.inner.card := by
  have h := inner_exposed_add_matching_card J hM_sub hM
  omega

/-- Predicate for a matching of `J` that leaves `v` as the unique exposed vertex of `J.verts`. -/
def IsTreeMatchingExposing (G : EdmondsMatching65.Polyhedron.Graph V E) (J : AltTree G) (v : V) (M : Finset E) : Prop :=
  M ⊆ J.edges ∧ IsMatching G M ∧ ∀ w ∈ J.verts, (PathsTreesFlowers.Duality.IsExposed G M w ↔ w = v)

lemma card_eq_inner_of_exposing {G : EdmondsMatching65.Polyhedron.Graph V E} (J : AltTree G) {v : V} (hv : v ∈ J.outer)
    {M : Finset E} (hM : IsTreeMatchingExposing G J v M) :
    M.card = J.inner.card := by
  have h := inner_exposed_add_matching_card J hM.1 hM.2.1
  have hempty : J.inner.filter (PathsTreesFlowers.Duality.IsExposed G M) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro u hu hexp
    have hu_verts : u ∈ J.verts := Finset.mem_union_left _ hu
    have huv : u = v := (hM.2.2 u hu_verts).mp hexp
    exact ne_of_mem_inner_of_mem_outer J hu hv huv
  rw [hempty, Finset.card_empty, zero_add] at h
  exact h

lemma exists_outer_exposed_of_card_eq_inner {G : EdmondsMatching65.Polyhedron.Graph V E} (J : AltTree G) {M : Finset E}
    (hM_sub : M ⊆ J.edges) (hM : IsMatching G M) (hcard : M.card = J.inner.card) :
    ∃ v ∈ J.outer, ∀ w ∈ J.verts, (PathsTreesFlowers.Duality.IsExposed G M w ↔ w = v) := by
  have hin := inner_exposed_add_matching_card J hM_sub hM
  have hout := outer_exposed_add_matching_card J hM_sub hM
  have hout_card := outer_card_eq_inner_card_add_one J
  have hin_zero : (J.inner.filter (PathsTreesFlowers.Duality.IsExposed G M)).card = 0 := by omega
  have hout_one : (J.outer.filter (PathsTreesFlowers.Duality.IsExposed G M)).card = 1 := by omega
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hin_zero
  obtain ⟨v, hv_eq⟩ := Finset.card_eq_one.mp hout_one
  have hv_mem : v ∈ J.outer.filter (PathsTreesFlowers.Duality.IsExposed G M) := by rw [hv_eq]; exact Finset.mem_singleton_self v
  have hv_outer : v ∈ J.outer := (Finset.mem_filter.mp hv_mem).1
  refine ⟨v, hv_outer, fun w hw => ?_⟩
  rcases Finset.mem_union.mp hw with hw_in | hw_out
  · constructor
    · intro hexp
      exact False.elim (hin_zero hw_in hexp)
    · rintro rfl
      exact False.elim (ne_of_mem_inner_of_mem_outer J hw_in hv_outer rfl)
  · have hiff : w ∈ J.outer.filter (PathsTreesFlowers.Duality.IsExposed G M) ↔ w = v := by
      rw [hv_eq, Finset.mem_singleton]
    rw [Finset.mem_filter, and_iff_right hw_out] at hiff
    exact hiff

/-! ### Part 4: Leaf-stripping induction on `J.inner.card` -/

lemma reflTransGen_first_step {G : EdmondsMatching65.Polyhedron.Graph V E} (J : AltTree G) {a b : V}
    (hab : Relation.ReflTransGen (fun x y => ∃ e ∈ J.edges, G.ends e = s(x, y)) a b) :
    a = b ∨ ∃ e ∈ J.edges, a ∈ G.ends e := by
  induction hab using Relation.ReflTransGen.head_induction_on with
  | refl => exact Or.inl rfl
  | head hstep _ _ =>
    rcases hstep with ⟨e, he, hends⟩
    exact Or.inr ⟨e, he, by rw [hends]; simp⟩

lemma outer_deg_pos {G : EdmondsMatching65.Polyhedron.Graph V E} (J : AltTree G) {u_any : V} (hu_any : u_any ∈ J.inner)
    {x : V} (hx : x ∈ J.outer) :
    1 ≤ (J.edges.filter (fun e => x ∈ G.ends e)).card := by
  have hx_verts : x ∈ J.inner ∪ J.outer := Finset.mem_union_right _ hx
  have hu_verts : u_any ∈ J.inner ∪ J.outer := Finset.mem_union_left _ hu_any
  have hpath := J.connected.2 x hx_verts u_any hu_verts
  rcases reflTransGen_first_step J hpath with h_eq | ⟨e, he, hxe⟩
  · exact False.elim (ne_of_mem_inner_of_mem_outer J hu_any hx h_eq.symm)
  · exact Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨he, hxe⟩⟩

lemma exists_leaf_outer_ne {G : EdmondsMatching65.Polyhedron.Graph V E} (J : AltTree G) {k : ℕ}
    (hinner : J.inner.card = k + 1) {v : V} (hv : v ∈ J.outer) :
    ∃ w₀ ∈ J.outer, w₀ ≠ v ∧ (J.edges.filter (fun e => w₀ ∈ G.ends e)).card = 1 := by
  obtain ⟨u_any, hu_any⟩ := Finset.card_pos.mp (by omega : 0 < J.inner.card)
  let deg : V → ℕ := fun x => (J.edges.filter (fun e => x ∈ G.ends e)).card
  have hsum_all : ∑ x ∈ J.outer, deg x = 2 * (k + 1) := by
    rw [sum_outer_deg_eq_edges_card J, edges_card_eq_two_mul_inner J, hinner]
  have hsum_erase : deg v + ∑ x ∈ J.outer.erase v, deg x = 2 * (k + 1) := by
    rw [Finset.add_sum_erase J.outer deg hv, hsum_all]
  have hdeg_v : 1 ≤ deg v := outer_deg_pos J hu_any hv
  have hcard_erase : (J.outer.erase v).card = k + 1 := by
    have hout := outer_card_eq_inner_card_add_one J
    have herase := Finset.card_erase_of_mem hv
    omega
  have hsum_two : ∑ _x ∈ J.outer.erase v, 2 = 2 * (k + 1) := by
    rw [Finset.sum_const, hcard_erase, smul_eq_mul, Nat.mul_comm]
  have hlt : ∑ x ∈ J.outer.erase v, deg x < ∑ _x ∈ J.outer.erase v, 2 := by
    rw [hsum_two]
    omega
  obtain ⟨w₀, hw₀_erase, hw₀_lt⟩ := Finset.exists_lt_of_sum_lt hlt
  have hw₀_ne : w₀ ≠ v := (Finset.mem_erase.mp hw₀_erase).1
  have hw₀_out : w₀ ∈ J.outer := (Finset.mem_erase.mp hw₀_erase).2
  have hw₀_ge : 1 ≤ deg w₀ := outer_deg_pos J hu_any hw₀_out
  refine ⟨w₀, hw₀_out, hw₀_ne, ?_⟩
  change deg w₀ = 1
  omega

/-- Pruned alternating tree obtained by stripping an outer leaf `w₀` (incident to `e₀ = s(u₀, w₀)`)
and its paired inner vertex `u₀` (also incident to `e₁ = s(u₀, w₁)`). -/
def pruneAltTree {G : EdmondsMatching65.Polyhedron.Graph V E} (J : AltTree G)
    (u₀ w₀ w₁ : V) (e₀ e₁ : E)
    (hu₀ : u₀ ∈ J.inner) (hw₀ : w₀ ∈ J.outer) (hw₁ : w₁ ∈ J.outer)
    (he₀ : e₀ ∈ J.edges) (he₁ : e₁ ∈ J.edges) (he₁_ne_e₀ : e₁ ≠ e₀)
    (hends_e₀ : G.ends e₀ = s(u₀, w₀)) (hends_e₁ : G.ends e₁ = s(u₀, w₁))
    (he₀_uniq : ∀ e ∈ J.edges, w₀ ∈ G.ends e → e = e₀)
    (hu₀_edges : ∀ e ∈ J.edges, u₀ ∈ G.ends e → e = e₀ ∨ e = e₁) :
    AltTree G where
  inner := J.inner.erase u₀
  outer := J.outer.erase w₀
  edges := (J.edges.erase e₀).erase e₁
  disjoint := J.disjoint.mono (Finset.erase_subset _ _) (Finset.erase_subset _ _)
  edge_ends := fun e he => by
    have he_ne_e₁ : e ≠ e₁ := (Finset.mem_erase.mp he).1
    have he_er₀ : e ∈ J.edges.erase e₀ := (Finset.mem_erase.mp he).2
    have he_ne_e₀ : e ≠ e₀ := (Finset.mem_erase.mp he_er₀).1
    have he_J : e ∈ J.edges := (Finset.mem_erase.mp he_er₀).2
    obtain ⟨u, hu, w, hw, hends⟩ := J.edge_ends e he_J
    have hu_ne : u ≠ u₀ := by
      rintro rfl
      have hu_mem : u ∈ G.ends e := by rw [hends]; simp
      rcases hu₀_edges e he_J hu_mem with rfl | rfl
      · exact he_ne_e₀ rfl
      · exact he_ne_e₁ rfl
    have hw_ne : w ≠ w₀ := by
      rintro rfl
      have hw_mem : w ∈ G.ends e := by rw [hends]; simp
      exact he_ne_e₀ (he₀_uniq e he_J hw_mem)
    exact ⟨u, Finset.mem_erase.mpr ⟨hu_ne, hu⟩, w, Finset.mem_erase.mpr ⟨hw_ne, hw⟩, hends⟩
  inner_deg := fun u hu => by
    have hu_ne : u ≠ u₀ := (Finset.mem_erase.mp hu).1
    have hu_in : u ∈ J.inner := (Finset.mem_erase.mp hu).2
    have hfilt : ((J.edges.erase e₀).erase e₁).filter (fun e => u ∈ G.ends e) =
        J.edges.filter (fun e => u ∈ G.ends e) := by
      ext e
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨⟨_, _, he⟩, hue⟩
        exact ⟨he, hue⟩
      · rintro ⟨he, hue⟩
        refine ⟨⟨?_, ?_, he⟩, hue⟩
        · rintro rfl
          rw [hends_e₁, Sym2.mem_iff] at hue
          rcases hue with rfl | rfl
          · exact hu_ne rfl
          · exact ne_of_mem_inner_of_mem_outer J hu_in hw₁ rfl
        · rintro rfl
          rw [hends_e₀, Sym2.mem_iff] at hue
          rcases hue with rfl | rfl
          · exact hu_ne rfl
          · exact ne_of_mem_inner_of_mem_outer J hu_in hw₀ rfl
    rw [hfilt]
    exact J.inner_deg u hu_in
  connected := by
    have hw₁_ne_w₀ : w₁ ≠ w₀ := by
      rintro rfl
      have hw₁_mem : w₁ ∈ G.ends e₁ := by rw [hends_e₁]; simp
      exact he₁_ne_e₀ (he₀_uniq e₁ he₁ hw₁_mem)
    have hw₁_mem : w₁ ∈ J.inner.erase u₀ ∪ J.outer.erase w₀ :=
      Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hw₁_ne_w₀, hw₁⟩)
    refine ⟨⟨w₁, hw₁_mem⟩, fun a ha b hb => ?_⟩
    let proj : V → V := fun x => if x = u₀ ∨ x = w₀ then w₁ else x
    have hproj_id : ∀ x ∈ J.inner.erase u₀ ∪ J.outer.erase w₀, proj x = x := by
      intro x hx
      dsimp [proj]
      rw [if_neg]
      rintro (rfl | rfl)
      · rcases Finset.mem_union.mp hx with hx_in | hx_out
        · exact (Finset.mem_erase.mp hx_in).1 rfl
        · exact not_mem_outer_of_mem_inner J hu₀ (Finset.mem_erase.mp hx_out).2
      · rcases Finset.mem_union.mp hx with hx_in | hx_out
        · exact not_mem_inner_of_mem_outer J hw₀ (Finset.mem_erase.mp hx_in).2
        · exact (Finset.mem_erase.mp hx_out).1 rfl
    have hstep : ∀ x y : V, (∃ e ∈ J.edges, G.ends e = s(x, y)) →
        Relation.ReflTransGen
          (fun p q => ∃ e ∈ (J.edges.erase e₀).erase e₁, G.ends e = s(p, q))
          (proj x) (proj y) := by
      rintro x y ⟨e, he, hends⟩
      by_cases he₀_eq : e = e₀
      · subst he₀_eq
        have hxy : (x = u₀ ∧ y = w₀) ∨ (x = w₀ ∧ y = u₀) := by
          rw [← Sym2.eq_iff, ← hends, hends_e₀]
        rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        · have hx_p : proj x = w₁ := if_pos (by tauto)
          have hy_p : proj y = w₁ := if_pos (by tauto)
          rw [hx_p, hy_p]
      · by_cases he₁_eq : e = e₁
        · subst he₁_eq
          have hxy : (x = u₀ ∧ y = w₁) ∨ (x = w₁ ∧ y = u₀) := by
            rw [← Sym2.eq_iff, ← hends, hends_e₁]
          have hw₁_p : proj w₁ = w₁ := by dsimp [proj]; split_ifs <;> rfl
          have hu₀_p : proj u₀ = w₁ := if_pos (Or.inl rfl)
          rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          · rw [hu₀_p, hw₁_p]
        · have he_pruned : e ∈ (J.edges.erase e₀).erase e₁ :=
            Finset.mem_erase.mpr ⟨he₁_eq, Finset.mem_erase.mpr ⟨he₀_eq, he⟩⟩
          have hx_not : ¬ (x = u₀ ∨ x = w₀) := by
            rintro (rfl | rfl)
            · have hx_mem : x ∈ G.ends e := by rw [hends]; simp
              rcases hu₀_edges e he hx_mem with rfl | rfl
              · exact he₀_eq rfl
              · exact he₁_eq rfl
            · have hx_mem : x ∈ G.ends e := by rw [hends]; simp
              exact he₀_eq (he₀_uniq e he hx_mem)
          have hy_not : ¬ (y = u₀ ∨ y = w₀) := by
            rintro (rfl | rfl)
            · have hy_mem : y ∈ G.ends e := by rw [hends]; simp
              rcases hu₀_edges e he hy_mem with rfl | rfl
              · exact he₀_eq rfl
              · exact he₁_eq rfl
            · have hy_mem : y ∈ G.ends e := by rw [hends]; simp
              exact he₀_eq (he₀_uniq e he hy_mem)
          have hx_p : proj x = x := if_neg hx_not
          have hy_p : proj y = y := if_neg hy_not
          rw [hx_p, hy_p]
          exact Relation.ReflTransGen.single ⟨e, he_pruned, hends⟩
    have hwalk : ∀ x y : V,
        Relation.ReflTransGen (fun p q => ∃ e ∈ J.edges, G.ends e = s(p, q)) x y →
        Relation.ReflTransGen
          (fun p q => ∃ e ∈ (J.edges.erase e₀).erase e₁, G.ends e = s(p, q))
          (proj x) (proj y) := by
      intro x y hxy
      induction hxy using Relation.ReflTransGen.head_induction_on with
      | refl => exact Relation.ReflTransGen.refl
      | head hst _ ih => exact Relation.ReflTransGen.trans (hstep _ _ hst) ih
    have ha_J : a ∈ J.inner ∪ J.outer :=
      Finset.union_subset_union (Finset.erase_subset _ _) (Finset.erase_subset _ _) ha
    have hb_J : b ∈ J.inner ∪ J.outer :=
      Finset.union_subset_union (Finset.erase_subset _ _) (Finset.erase_subset _ _) hb
    have h_ab := hwalk a b (J.connected.2 a ha_J b hb_J)
    rwa [hproj_id a ha, hproj_id b hb] at h_ab
  card_verts := by
    have hdisj' : Disjoint (J.inner.erase u₀) (J.outer.erase w₀) :=
      J.disjoint.mono (Finset.erase_subset _ _) (Finset.erase_subset _ _)
    have hverts' : (J.inner.erase u₀ ∪ J.outer.erase w₀).card =
        (J.inner.erase u₀).card + (J.outer.erase w₀).card :=
      Finset.card_union_of_disjoint hdisj'
    have hverts : (J.inner ∪ J.outer).card = J.inner.card + J.outer.card :=
      Finset.card_union_of_disjoint J.disjoint
    have hin_er : (J.inner.erase u₀).card = J.inner.card - 1 := Finset.card_erase_of_mem hu₀
    have hout_er : (J.outer.erase w₀).card = J.outer.card - 1 := Finset.card_erase_of_mem hw₀
    have hin_pos : 1 ≤ J.inner.card := Finset.card_pos.mpr ⟨u₀, hu₀⟩
    have hout_pos : 1 ≤ J.outer.card := Finset.card_pos.mpr ⟨w₀, hw₀⟩
    have he₁_er₀ : e₁ ∈ J.edges.erase e₀ := Finset.mem_erase.mpr ⟨he₁_ne_e₀, he₁⟩
    have hed_er₁ : ((J.edges.erase e₀).erase e₁).card = (J.edges.erase e₀).card - 1 :=
      Finset.card_erase_of_mem he₁_er₀
    have hed_er₀ : (J.edges.erase e₀).card = J.edges.card - 1 :=
      Finset.card_erase_of_mem he₀
    have hed_pos : 2 ≤ J.edges.card := by
      have := edges_card_eq_two_mul_inner J
      omega
    have hcard := J.card_verts
    omega

lemma existsUnique_treeMatchingExposing_aux {G : EdmondsMatching65.Polyhedron.Graph V E} :
    ∀ (k : ℕ) (J : AltTree G), J.inner.card = k →
      ∀ v ∈ J.outer, ∃! MJ : Finset E, IsTreeMatchingExposing G J v MJ
  | 0, J, hinner, v, hv => by
    have hin_empty : J.inner = ∅ := Finset.card_eq_zero.mp hinner
    have hed_card : J.edges.card = 0 := by
      rw [edges_card_eq_two_mul_inner J, hinner]
    have hed_empty : J.edges = ∅ := Finset.card_eq_zero.mp hed_card
    have hout_card : J.outer.card = 1 := by
      rw [outer_card_eq_inner_card_add_one J, hinner]
    have hout_eq : J.outer = {v} := by
      obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hout_card
      have hvx : v = x := Finset.mem_singleton.mp (hx ▸ hv)
      rw [hx, hvx]
    have hverts_eq : J.verts = {v} := by
      change J.inner ∪ J.outer = {v}
      rw [hin_empty, hout_eq, Finset.empty_union]
    refine ⟨∅, ⟨?_, ?_, ?_⟩, ?_⟩
    · exact Finset.empty_subset _
    · intro e he
      exact False.elim (Finset.notMem_empty e he)
    · intro w hw
      rw [hverts_eq, Finset.mem_singleton] at hw
      subst hw
      simp only [iff_true]
      intro e he
      exact False.elim (Finset.notMem_empty e he)
    · intro MJ hMJ
      have hsub : MJ ⊆ ∅ := hed_empty ▸ hMJ.1
      exact Finset.subset_empty.mp hsub
  | k + 1, J, hinner, v, hv => by
    obtain ⟨w₀, hw₀, hw₀_ne_v, hdeg_w₀⟩ := exists_leaf_outer_ne J hinner hv
    obtain ⟨e₀, he₀_filt⟩ := Finset.card_eq_one.mp hdeg_w₀
    have he₀_mem_filt : e₀ ∈ J.edges.filter (fun e => w₀ ∈ G.ends e) := by
      rw [he₀_filt]; exact Finset.mem_singleton_self e₀
    have he₀ : e₀ ∈ J.edges := (Finset.mem_filter.mp he₀_mem_filt).1
    have hw₀_e₀ : w₀ ∈ G.ends e₀ := (Finset.mem_filter.mp he₀_mem_filt).2
    have he₀_uniq : ∀ e ∈ J.edges, w₀ ∈ G.ends e → e = e₀ := by
      intro e he hwe
      have hmem : e ∈ J.edges.filter (fun e => w₀ ∈ G.ends e) := Finset.mem_filter.mpr ⟨he, hwe⟩
      rw [he₀_filt, Finset.mem_singleton] at hmem
      exact hmem
    obtain ⟨u₀, hu₀, w₀', hw₀', hends_e₀'⟩ := J.edge_ends e₀ he₀
    have hw₀'_eq : w₀' = w₀ := by
      have hmem := hw₀_e₀
      rw [hends_e₀', Sym2.mem_iff] at hmem
      rcases hmem with rfl | rfl
      · exact False.elim (ne_of_mem_inner_of_mem_outer J hu₀ hw₀ rfl)
      · rfl
    have hends_e₀ : G.ends e₀ = s(u₀, w₀) := hw₀'_eq ▸ hends_e₀'
    have hu₀_e₀ : u₀ ∈ G.ends e₀ := by rw [hends_e₀]; simp
    have he₀_u₀_filt : e₀ ∈ J.edges.filter (fun e => u₀ ∈ G.ends e) :=
      Finset.mem_filter.mpr ⟨he₀, hu₀_e₀⟩
    have hcard_u₀_erase : ((J.edges.filter (fun e => u₀ ∈ G.ends e)).erase e₀).card = 1 := by
      rw [Finset.card_erase_of_mem he₀_u₀_filt, J.inner_deg u₀ hu₀]
    obtain ⟨e₁, he₁_filt⟩ := Finset.card_eq_one.mp hcard_u₀_erase
    have he₁_mem_erase : e₁ ∈ (J.edges.filter (fun e => u₀ ∈ G.ends e)).erase e₀ := by
      rw [he₁_filt]; exact Finset.mem_singleton_self e₁
    have he₁_ne_e₀ : e₁ ≠ e₀ := (Finset.mem_erase.mp he₁_mem_erase).1
    have he₁_u₀_filt : e₁ ∈ J.edges.filter (fun e => u₀ ∈ G.ends e) :=
      (Finset.mem_erase.mp he₁_mem_erase).2
    have he₁ : e₁ ∈ J.edges := (Finset.mem_filter.mp he₁_u₀_filt).1
    have hu₀_e₁ : u₀ ∈ G.ends e₁ := (Finset.mem_filter.mp he₁_u₀_filt).2
    have hu₀_edges : ∀ e ∈ J.edges, u₀ ∈ G.ends e → e = e₀ ∨ e = e₁ := by
      intro e he hue
      by_cases he_e₀ : e = e₀
      · exact Or.inl he_e₀
      · have hmem : e ∈ (J.edges.filter (fun e => u₀ ∈ G.ends e)).erase e₀ :=
          Finset.mem_erase.mpr ⟨he_e₀, Finset.mem_filter.mpr ⟨he, hue⟩⟩
        rw [he₁_filt, Finset.mem_singleton] at hmem
        exact Or.inr hmem
    obtain ⟨u₀', hu₀', w₁, hw₁, hends_e₁'⟩ := J.edge_ends e₁ he₁
    have hu₀'_eq : u₀' = u₀ := by
      have hmem := hu₀_e₁
      rw [hends_e₁', Sym2.mem_iff] at hmem
      rcases hmem with rfl | rfl
      · rfl
      · exact False.elim (ne_of_mem_inner_of_mem_outer J hu₀ hw₁ rfl)
    have hends_e₁ : G.ends e₁ = s(u₀, w₁) := hu₀'_eq ▸ hends_e₁'
    let J' := pruneAltTree J u₀ w₀ w₁ e₀ e₁ hu₀ hw₀ hw₁ he₀ he₁ he₁_ne_e₀
      hends_e₀ hends_e₁ he₀_uniq hu₀_edges
    have hJ'_inner : J'.inner.card = k := by
      change (J.inner.erase u₀).card = k
      rw [Finset.card_erase_of_mem hu₀, hinner]
      rfl
    have hv_J' : v ∈ J'.outer := Finset.mem_erase.mpr ⟨hw₀_ne_v.symm, hv⟩
    have hnot_ends_of_mem_J' : ∀ e ∈ J'.edges, u₀ ∉ G.ends e ∧ w₀ ∉ G.ends e := by
      intro e he
      have he_ne_e₁ : e ≠ e₁ := (Finset.mem_erase.mp he).1
      have he_er₀ : e ∈ J.edges.erase e₀ := (Finset.mem_erase.mp he).2
      have he_ne_e₀ : e ≠ e₀ := (Finset.mem_erase.mp he_er₀).1
      have he_J : e ∈ J.edges := (Finset.mem_erase.mp he_er₀).2
      refine ⟨fun hu => ?_, fun hw => he_ne_e₀ (he₀_uniq e he_J hw)⟩
      rcases hu₀_edges e he_J hu with rfl | rfl
      · exact he_ne_e₀ rfl
      · exact he_ne_e₁ rfl
    have h_insert_exposing : ∀ MJ' : Finset E,
        IsTreeMatchingExposing G J' v MJ' → IsTreeMatchingExposing G J v (insert e₀ MJ') := by
      intro MJ' hMJ'
      have hMJ'_sub_J : MJ' ⊆ J.edges :=
        hMJ'.1.trans ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _))
      refine ⟨Finset.insert_subset he₀ hMJ'_sub_J, ?_, ?_⟩
      · intro e he f hf hef x hxe hxf
        rcases Finset.mem_insert.mp he with rfl | he' <;>
          rcases Finset.mem_insert.mp hf with rfl | hf'
        · exact hef rfl
        · rw [hends_e₀, Sym2.mem_iff] at hxe
          rcases hxe with rfl | rfl
          · exact (hnot_ends_of_mem_J' f (hMJ'.1 hf')).1 hxf
          · exact (hnot_ends_of_mem_J' f (hMJ'.1 hf')).2 hxf
        · rw [hends_e₀, Sym2.mem_iff] at hxf
          rcases hxf with rfl | rfl
          · exact (hnot_ends_of_mem_J' e (hMJ'.1 he')).1 hxe
          · exact (hnot_ends_of_mem_J' e (hMJ'.1 he')).2 hxe
        · exact hMJ'.2.1 e he' f hf' hef x hxe hxf
      · intro w hw
        have hexp_ins : PathsTreesFlowers.Duality.IsExposed G (insert e₀ MJ') w ↔ w ∉ G.ends e₀ ∧ PathsTreesFlowers.Duality.IsExposed G MJ' w := by
          unfold PathsTreesFlowers.Duality.IsExposed
          exact Finset.forall_mem_insert _ _ _
        by_cases hw_u₀ : w = u₀
        · subst w
          have huv : u₀ ≠ v := ne_of_mem_inner_of_mem_outer J hu₀ hv
          rw [hexp_ins]
          exact ⟨fun h => False.elim (h.1 hu₀_e₀), fun h => False.elim (huv h)⟩
        · by_cases hw_w₀ : w = w₀
          · subst w
            rw [hexp_ins]
            exact ⟨fun h => False.elim (h.1 hw₀_e₀), fun h => False.elim (hw₀_ne_v h)⟩
          · have hw_not_e₀ : w ∉ G.ends e₀ := by
              rw [hends_e₀, Sym2.mem_iff]
              rintro (rfl | rfl)
              · exact hw_u₀ rfl
              · exact hw_w₀ rfl
            have hw_J' : w ∈ J'.verts := by
              rcases Finset.mem_union.mp hw with hw_in | hw_out
              · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hw_u₀, hw_in⟩)
              · exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hw_w₀, hw_out⟩)
            rw [hexp_ins, and_iff_right hw_not_e₀]
            exact hMJ'.2.2 w hw_J'
    have h_erase_exposing : ∀ MJ : Finset E,
        IsTreeMatchingExposing G J v MJ →
          e₀ ∈ MJ ∧ IsTreeMatchingExposing G J' v (MJ.erase e₀) := by
      intro MJ hMJ
      have hw₀_verts : w₀ ∈ J.verts := Finset.mem_union_right _ hw₀
      have hnot_exp_w₀ : ¬ PathsTreesFlowers.Duality.IsExposed G MJ w₀ := fun hexp => hw₀_ne_v ((hMJ.2.2 w₀ hw₀_verts).mp hexp)
      simp only [PathsTreesFlowers.Duality.IsExposed, not_forall, not_not] at hnot_exp_w₀
      rcases hnot_exp_w₀ with ⟨e, he_MJ, hw₀_e⟩
      have he_eq_e₀ : e = e₀ := he₀_uniq e (hMJ.1 he_MJ) hw₀_e
      have he₀_MJ : e₀ ∈ MJ := he_eq_e₀ ▸ he_MJ
      have he₁_not_MJ : e₁ ∉ MJ := by
        intro he₁_MJ
        exact hMJ.2.1 e₁ he₁_MJ e₀ he₀_MJ he₁_ne_e₀ u₀ hu₀_e₁ hu₀_e₀
      refine ⟨he₀_MJ, ?_, ?_, ?_⟩
      · intro f hf
        have hf_ne_e₀ : f ≠ e₀ := (Finset.mem_erase.mp hf).1
        have hf_MJ : f ∈ MJ := (Finset.mem_erase.mp hf).2
        have hf_ne_e₁ : f ≠ e₁ := fun h => he₁_not_MJ (h ▸ hf_MJ)
        exact Finset.mem_erase.mpr ⟨hf_ne_e₁, Finset.mem_erase.mpr ⟨hf_ne_e₀, hMJ.1 hf_MJ⟩⟩
      · intro f₁ hf₁ f₂ hf₂ hf₁₂ x hx₁ hx₂
        exact hMJ.2.1 f₁ (Finset.mem_erase.mp hf₁).2 f₂ (Finset.mem_erase.mp hf₂).2 hf₁₂ x hx₁ hx₂
      · intro w hw'
        have hw_J : w ∈ J.verts :=
          Finset.union_subset_union (Finset.erase_subset _ _) (Finset.erase_subset _ _) hw'
        have hw_not_e₀ : w ∉ G.ends e₀ := by
          rw [hends_e₀, Sym2.mem_iff]
          rintro (rfl | rfl)
          · rcases Finset.mem_union.mp hw' with hw_in | hw_out
            · exact (Finset.mem_erase.mp hw_in).1 rfl
            · exact not_mem_outer_of_mem_inner J hu₀ (Finset.mem_erase.mp hw_out).2
          · rcases Finset.mem_union.mp hw' with hw_in | hw_out
            · exact not_mem_inner_of_mem_outer J hw₀ (Finset.mem_erase.mp hw_in).2
            · exact (Finset.mem_erase.mp hw_out).1 rfl
        have hexp_ins : PathsTreesFlowers.Duality.IsExposed G (insert e₀ (MJ.erase e₀)) w ↔
            w ∉ G.ends e₀ ∧ PathsTreesFlowers.Duality.IsExposed G (MJ.erase e₀) w := by
          unfold PathsTreesFlowers.Duality.IsExposed
          exact Finset.forall_mem_insert _ _ _
        rw [Finset.insert_erase he₀_MJ, and_iff_right hw_not_e₀] at hexp_ins
        rw [← hexp_ins]
        exact hMJ.2.2 w hw_J
    obtain ⟨MJ', hMJ', hMJ'_uniq⟩ := existsUnique_treeMatchingExposing_aux k J' hJ'_inner v hv_J'
    refine ⟨insert e₀ MJ', h_insert_exposing MJ' hMJ', ?_⟩
    intro MJ hMJ
    obtain ⟨he₀_MJ, hMJ_er⟩ := h_erase_exposing MJ hMJ
    have her_eq : MJ.erase e₀ = MJ' := hMJ'_uniq (MJ.erase e₀) hMJ_er
    rw [← Finset.insert_erase he₀_MJ, her_eq]

/-! ### Part 5: Combining everything for `lemma_4_2` -/

lemma isMaxMatchingOn_iff_card_eq_inner {G : EdmondsMatching65.Polyhedron.Graph V E} (J : AltTree G) (M : Finset E) :
    IsMaxMatchingOn G J.edges M ↔
      M ⊆ J.edges ∧ IsMatching G M ∧ M.card = J.inner.card := by
  constructor
  · intro hMax
    have hle : M.card ≤ J.inner.card := matching_card_le_inner_card J hMax.1 hMax.2.1
    have hout_pos : 0 < J.outer.card := by
      rw [outer_card_eq_inner_card_add_one J]; omega
    obtain ⟨v₀, hv₀⟩ := Finset.card_pos.mp hout_pos
    obtain ⟨M₀, hM₀, -⟩ := existsUnique_treeMatchingExposing_aux J.inner.card J rfl v₀ hv₀
    have hM₀_card : M₀.card = J.inner.card := card_eq_inner_of_exposing J hv₀ hM₀
    have hge : J.inner.card ≤ M.card := hM₀_card ▸ hMax.2.2 M₀ hM₀.1 hM₀.2.1
    exact ⟨hMax.1, hMax.2.1, le_antisymm hle hge⟩
  · rintro ⟨hsub, hM, hcard⟩
    refine ⟨hsub, hM, fun M' hM'_sub hM' => ?_⟩
    rw [hcard]
    exact matching_card_le_inner_card J hM'_sub hM'

lemma isMaxMatchingOn_and_exposing_iff {G : EdmondsMatching65.Polyhedron.Graph V E} (J : AltTree G) {v : V} (hv : v ∈ J.outer)
    (M : Finset E) :
    (IsMaxMatchingOn G J.edges M ∧ ∀ w ∈ J.verts, (PathsTreesFlowers.Duality.IsExposed G M w ↔ w = v)) ↔
      IsTreeMatchingExposing G J v M := by
  rw [isMaxMatchingOn_iff_card_eq_inner]
  constructor
  · rintro ⟨⟨hsub, hM, _⟩, hexp⟩
    exact ⟨hsub, hM, hexp⟩
  · intro h
    exact ⟨⟨h.1, h.2.1, card_eq_inner_of_exposing J hv h⟩, h.2.2⟩

end SolPathsTreesFlowersLemma42

open EdmondsMatching65.Polyhedron (IsMatching)
open PathsTreesFlowers.Duality (AltTree IsMaxMatchingOn)
open SolPathsTreesFlowersLemma42

theorem solution {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E)
    (J : AltTree G) :
    J.outer.card = J.inner.card + 1 ∧
    (∀ v ∈ J.outer, ∃! MJ : Finset E, IsMaxMatchingOn G J.edges MJ ∧
        ∀ w ∈ J.verts, (PathsTreesFlowers.Duality.IsExposed G MJ w ↔ w = v)) ∧
    (∀ MJ : Finset E, IsMaxMatchingOn G J.edges MJ →
        ∃ v ∈ J.outer, ∀ w ∈ J.verts, (PathsTreesFlowers.Duality.IsExposed G MJ w ↔ w = v)) := by
  refine ⟨outer_card_eq_inner_card_add_one J, ?_, ?_⟩
  · intro v hv
    simp_rw [isMaxMatchingOn_and_exposing_iff J hv]
    exact existsUnique_treeMatchingExposing_aux J.inner.card J rfl v hv
  · intro MJ hMJ
    rw [isMaxMatchingOn_iff_card_eq_inner] at hMJ
    exact exists_outer_exposed_of_card_eq_inner J hMJ.1 hMJ.2.1 hMJ.2.2
