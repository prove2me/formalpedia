-- Prove2me | solution 1 for TreewidthApprox.TreeMeasure.case_two_or_more
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-11T03:58:30.805454+00:00
-- url     : https://prove2.me/submissions/bf2ecc99-9f8c-46e4-b07b-33ca868d315a

import Mathlib
import Definitions.Def_HarelTarjan_Compressed_RootedTree
import Definitions.Def_TreewidthApprox_TreeMeasure_Setting
open HarelTarjan.Compressed TreewidthApprox.TreeMeasure

private theorem anc_trans {V : Type*} [Fintype V] [DecidableEq V] (T : RootedTree V)
    {a b u : V} (hab : IsAncestor T a b) (hbu : IsAncestor T b u) : IsAncestor T a u := by
  obtain ⟨m, hm⟩ := hab
  obtain ⟨n, hn⟩ := hbu
  exact ⟨m+n, by rw [Function.iterate_add_apply, hn, hm]⟩

private theorem anc_compare {V : Type*} [Fintype V] [DecidableEq V] (T : RootedTree V)
    {a b u : V} (ha : IsAncestor T a u) (hb : IsAncestor T b u) :
    IsAncestor T a b ∨ IsAncestor T b a := by
  obtain ⟨m, hm⟩ := ha
  obtain ⟨n, hn⟩ := hb
  rcases le_total m n with h | h
  · right
    refine ⟨n-m, ?_⟩
    rw [← hm, ← Function.iterate_add_apply, Nat.sub_add_cancel h, hn]
  · left
    refine ⟨m-n, ?_⟩
    rw [← hn, ← Function.iterate_add_apply, Nat.sub_add_cancel h, hm]

private theorem weight_child {V : Type*} [Fintype V] [DecidableEq V] (T : RootedTree V)
    (μ : V → ℝ) (C : ℝ) (hC : C < 1) (h₁ : ∀ v, 1 ≤ μ v)
    (h₃ : ∀ v c, IsChild T v c → μ c ≤ C * μ v) {v c : V} (hc : IsChild T v c) :
    μ c < μ v := by
  have := h₃ v c hc
  have := h₁ v
  nlinarith

private theorem weight_anc {V : Type*} [Fintype V] [DecidableEq V] (T : RootedTree V)
    (μ : V → ℝ) (C : ℝ) (hC : C < 1) (h₁ : ∀ v, 1 ≤ μ v)
    (h₃ : ∀ v c, IsChild T v c → μ c ≤ C * μ v) {v u : V} (h : IsAncestor T v u) :
    μ u ≤ μ v := by
  obtain ⟨n, rfl⟩ := h
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    refine ih.trans ?_
    by_cases he : T.parent^[n] u = T.root
    · rw [he, T.parent_root]
    · exact (weight_child T μ C hC h₁ h₃ ⟨he, rfl⟩).le

private theorem children_incomparable {V : Type*} [Fintype V] [DecidableEq V] (T : RootedTree V)
    (μ : V → ℝ) (C : ℝ) (hC : C < 1) (h₁ : ∀ v, 1 ≤ μ v)
    (h₃ : ∀ v c, IsChild T v c → μ c ≤ C * μ v) {v a b : V}
    (ha : IsChild T v a) (hb : IsChild T v b) (hab : IsAncestor T a b) : a = b := by
  obtain ⟨n, hn⟩ := hab
  cases n with
  | zero => simpa using hn.symm
  | succ n =>
    have hn' : IsAncestor T a v := ⟨n, by simpa [Function.iterate_succ_apply, hb.2] using hn⟩
    have hm := weight_anc T μ C hC h₁ h₃ hn'
    have hl := weight_child T μ C hC h₁ h₃ ha
    linarith

private theorem anc_split {V : Type*} [Fintype V] [DecidableEq V] (T : RootedTree V)
    (v u : V) : IsAncestor T v u ↔ u = v ∨ ∃ c ∈ children T v, IsAncestor T c u := by
  classical
  constructor
  · intro h
    let n := Nat.find h
    have hn : T.parent^[n] u = v := Nat.find_spec h
    cases he : n with
    | zero => exact Or.inl (by simpa [he] using hn)
    | succ k =>
      right
      refine ⟨T.parent^[k] u, ?_, k, rfl⟩
      have hp : T.parent (T.parent^[k] u) = v := by
        simpa [he, Function.iterate_succ_apply'] using hn
      have hnr : T.parent^[k] u ≠ T.root := by
        intro hr
        have hv : v = T.root := by rw [hr, T.parent_root] at hp; exact hp.symm
        have hlt : k < Nat.find h := by change k < n; omega
        exact Nat.find_min h hlt (by simpa [hv] using hr)
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnr, hp⟩
  · rintro (rfl | ⟨c, hc, hu⟩)
    · exact ⟨0, rfl⟩
    · have hcv : IsChild T v c := (Finset.mem_filter.mp hc).2
      exact anc_trans T ⟨1, by simpa using hcv.2⟩ hu

private theorem size_rec {V : Type*} [Fintype V] [DecidableEq V] (T : RootedTree V)
    (μ : V → ℝ) (C : ℝ) (hC : C < 1) (h₁ : ∀ v, 1 ≤ μ v)
    (h₃ : ∀ v c, IsChild T v c → μ c ≤ C * μ v) (v : V) :
    size T v = 1 + ∑ c ∈ children T v, size T c := by
  classical
  let D (a : V) := Finset.univ.filter (fun u => IsAncestor T a u)
  have hd : (↑(children T v) : Set V).PairwiseDisjoint D := by
    intro a ha b hb hab
    apply Finset.disjoint_left.mpr
    intro u hua hub
    have ha' : IsChild T v a := (Finset.mem_filter.mp ha).2
    have hb' : IsChild T v b := (Finset.mem_filter.mp hb).2
    rcases anc_compare T (Finset.mem_filter.mp hua).2 (Finset.mem_filter.mp hub).2 with h | h
    · exact hab (children_incomparable T μ C hC h₁ h₃ ha' hb' h)
    · exact hab (children_incomparable T μ C hC h₁ h₃ hb' ha' h).symm
  have hv : v ∉ (children T v).biUnion D := by
    simp only [Finset.mem_biUnion, not_exists, not_and]
    intro c hc hv
    have hl := weight_child T μ C hC h₁ h₃ (Finset.mem_filter.mp hc).2
    have hm := weight_anc T μ C hC h₁ h₃ (Finset.mem_filter.mp hv).2
    linarith
  have heq : D v = insert v ((children T v).biUnion D) := by
    ext u
    simp only [D, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_biUnion]
    exact anc_split T v u
  change (D v).card = 1 + ∑ c ∈ children T v, (D c).card
  rw [heq, Finset.card_insert_of_notMem hv, Finset.card_biUnion hd]
  omega

private theorem size_child_lt {V : Type*} [Fintype V] [DecidableEq V] (T : RootedTree V)
    (μ : V → ℝ) (C : ℝ) (hC : C < 1) (h₁ : ∀ v, 1 ≤ μ v)
    (h₃ : ∀ v c, IsChild T v c → μ c ≤ C * μ v) {v c : V} (hc : c ∈ children T v) :
    size T c < size T v := by
  rw [size_rec T μ C hC h₁ h₃ v]
  have hle : size T c ≤ ∑ a ∈ children T v, size T a :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) hc
  omega


private theorem base_bound {V : Type*} [Fintype V] [DecidableEq V] (T : RootedTree V)
    (μ : V → ℝ) (C : ℝ) (hC₀ : 0 < C) (hC₁ : C < 1)
    (h₁ : ∀ v, 1 ≤ μ v)
    (h₃ : ∀ v c, IsChild T v c → μ c ≤ C * μ v)
    (v : V) (hleaf : children T v = ∅) :
    (size T v : ℝ) ≤ (1 + 1 / (1 - C)) * μ v - 1 := by
  have hs := size_rec T μ C hC₁ h₁ h₃ v
  simp only [hleaf, Finset.sum_empty, add_zero] at hs
  rw [hs]
  have hd : 1 ≤ 1 / (1 - C) := (le_div_iff₀ (by linarith)).mpr (by linarith)
  have hm := h₁ v
  norm_num only [Nat.cast_one]
  have hmul := mul_le_mul_of_nonneg_right hd (show 0 ≤ μ v by linarith)
  nlinarith

private theorem summed {V : Type*} [Fintype V] [DecidableEq V] (T : RootedTree V)
    (μ : V → ℝ) (C : ℝ) (hC₁ : C < 1)
    (h₁ : ∀ v, 1 ≤ μ v)
    (h₃ : ∀ v c, IsChild T v c → μ c ≤ C * μ v)
    (v : V)
    (hIH : ∀ c ∈ children T v, (size T c : ℝ) ≤ (1 + 1 / (1 - C)) * μ c - 1) :
    (size T v : ℝ) ≤
      1 - ((children T v).card : ℝ) + (1 + 1 / (1 - C)) * ∑ c ∈ children T v, μ c := by
  classical
  have hr : (size T v : ℝ) = 1 + ∑ c ∈ children T v, (size T c : ℝ) := by
    exact_mod_cast size_rec T μ C hC₁ h₁ h₃ v
  calc
    (size T v : ℝ) = 1 + ∑ c ∈ children T v, (size T c : ℝ) := hr
    _ ≤ 1 + ∑ c ∈ children T v, ((1 + 1 / (1 - C)) * μ c - 1) := by
      exact add_le_add_right (Finset.sum_le_sum hIH) 1
    _ = _ := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      simp
      ring

private theorem many_bound {V : Type*} [Fintype V] [DecidableEq V] (T : RootedTree V)
    (μ : V → ℝ) (C : ℝ) (hC₁ : C < 1)
    (h₁ : ∀ v, 1 ≤ μ v)
    (h₂ : ∀ v, ∑ c ∈ children T v, μ c ≤ μ v)
    (h₃ : ∀ v c, IsChild T v c → μ c ≤ C * μ v)
    (v : V) (hp : 2 ≤ (children T v).card)
    (hIH : ∀ c ∈ children T v, (size T c : ℝ) ≤ (1 + 1 / (1 - C)) * μ c - 1) :
    (size T v : ℝ) ≤ (1 + 1 / (1 - C)) * μ v - 1 := by
  have hb := summed T μ C hC₁ h₁ h₃ v hIH
  have hp' : (2 : ℝ) ≤ ((children T v).card : ℝ) := by exact_mod_cast hp
  have hk : 0 ≤ 1 + 1 / (1 - C) := by positivity
  have hm := mul_le_mul_of_nonneg_left (h₂ v) hk
  linarith

private theorem one_bound {V : Type*} [Fintype V] [DecidableEq V] (T : RootedTree V)
    (μ : V → ℝ) (C : ℝ) (hC₁ : C < 1)
    (h₁ : ∀ v, 1 ≤ μ v)
    (h₃ : ∀ v c, IsChild T v c → μ c ≤ C * μ v)
    (v : V) (hp : (children T v).card = 1)
    (hIH : ∀ c ∈ children T v, (size T c : ℝ) ≤ (1 + 1 / (1 - C)) * μ c - 1) :
    (size T v : ℝ) ≤ (1 + 1 / (1 - C)) * μ v - 1 := by
  classical
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hp
  have hmem : c ∈ children T v := by rw [hc]; simp
  have hb := summed T μ C hC₁ h₁ h₃ v hIH
  simp only [hc, Finset.card_singleton, Nat.cast_one, sub_self, Finset.sum_singleton, zero_add] at hb
  have hh := h₃ v c (Finset.mem_filter.mp hmem).2
  have hk : 0 ≤ 1 + 1 / (1 - C) := by positivity
  have hm := mul_le_mul_of_nonneg_left hh hk
  have hid : (1 + 1 / (1 - C)) * (1 - C) = 2 - C := by
    have hz : 1 - C ≠ 0 := ne_of_gt (by linarith)
    field_simp [hz]
    <;> ring
  have hpos : 0 < 1 - C := by linarith
  have hmul : 1 ≤ (2 - C) * μ v := by nlinarith [h₁ v]
  have hid' := congrArg (fun z : ℝ => z * μ v) hid
  nlinarith

private theorem all_bound {V : Type*} [Fintype V] [DecidableEq V] (T : RootedTree V)
    (μ : V → ℝ) (C : ℝ) (hC₀ : 0 < C) (hC₁ : C < 1)
    (h₁ : ∀ v, 1 ≤ μ v)
    (h₂ : ∀ v, ∑ c ∈ children T v, μ c ≤ μ v)
    (h₃ : ∀ v c, IsChild T v c → μ c ≤ C * μ v) :
    ∀ v, (size T v : ℝ) ≤ (1 + 1 / (1 - C)) * μ v - 1 := by
  classical
  have hclaim : ∀ k : ℕ, ∀ v : V, size T v = k →
      (size T v : ℝ) ≤ (1 + 1 / (1 - C)) * μ v - 1 := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro v hv
      have hIH : ∀ c ∈ children T v, (size T c : ℝ) ≤ (1 + 1 / (1 - C)) * μ c - 1 := by
        intro c hc
        exact ih (size T c) (by rw [← hv]; exact size_child_lt T μ C hC₁ h₁ h₃ hc) c rfl
      by_cases he : (children T v).card = 0
      · exact base_bound T μ C hC₀ hC₁ h₁ h₃ v (Finset.card_eq_zero.mp he)
      by_cases ho : (children T v).card = 1
      · exact one_bound T μ C hC₁ h₁ h₃ v ho hIH
      · exact many_bound T μ C hC₁ h₁ h₂ h₃ v (by omega) hIH
  intro v
  exact hclaim (size T v) v rfl



open HarelTarjan.Compressed

theorem solution {V : Type*} [Fintype V] [DecidableEq V] (T : RootedTree V)
    (μ : V → ℝ) (C : ℝ) (hC₀ : 0 < C) (hC₁ : C < 1)
    (h₁ : ∀ v, 1 ≤ μ v)
    (h₂ : ∀ v, ∑ c ∈ children T v, μ c ≤ μ v)
    (h₃ : ∀ v c, IsChild T v c → μ c ≤ C * μ v)
    (v : V) (hp : 2 ≤ (children T v).card)
    (hIH : ∀ c ∈ children T v, (size T c : ℝ) ≤ (1 + 1 / (1 - C)) * μ c - 1) :
    (size T v : ℝ) ≤ (1 + 1 / (1 - C)) * μ v - 1 := by exact many_bound T μ C hC₁ h₁ h₂ h₃ v hp hIH

