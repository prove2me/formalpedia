-- Prove2me | solution 1 for PaigeTarjan.LexSort.lemma1_invariant
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T07:44:06.474805+00:00
-- url     : https://prove2.me/submissions/e0ff92d7-00c6-49c5-8b2a-87efca70a1cf

import Mathlib
import Definitions.Def_PaigeTarjan_LexSort_Basic
import Definitions.Def_PaigeTarjan_LexSort_Refine

set_option autoImplicit false

theorem pt2076_prefix_concat_iff {A : Type} (α l : List A) (u : A) :
    (α ++ [u]) <+: l ↔ α <+: l ∧ l[α.length]? = some u := by
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨⟨[u] ++ t, by simp⟩, ?_⟩
    simp
  · rintro ⟨⟨t, rfl⟩, h⟩
    cases t with
    | nil => simp at h
    | cons v t =>
      simp at h
      subst h
      exact ⟨t, by simp⟩

theorem pt2076_proper_prefix_extend {A : Type} (α l : List A) (h : α <+: l) (hne : α ≠ l) :
    ∃ u, (α ++ [u]) <+: l := by
  obtain ⟨t, rfl⟩ := h
  cases t with
  | nil => simp at hne
  | cons v t => exact ⟨v, t, by simp⟩

open PaigeTarjan.LexSort in
theorem pt2076_dp_prefix {k n : ℕ} (x : Fin n → List (Fin (k + 1))) (i : Fin n) :
    dp x i <+: x i := by
  unfold dp
  split_ifs
  · exact List.prefix_refl _
  · exact List.take_prefix _ _

open PaigeTarjan.LexSort in
theorem pt2076_mem_children {k n : ℕ} (x : Fin n → List (Fin (k + 1)))
    (α : List (Fin (k + 1))) (u : Fin (k + 1)) (i : Fin n) (h : (α ++ [u]) <+: x i) :
    α ++ [u] ∈ children x α := by
  unfold children blk
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨u, ⟨i, (pt2076_prefix_concat_iff _ _ _).1 h⟩, rfl⟩

open PaigeTarjan.LexSort in
theorem pt2076_step {k n : ℕ} (x : Fin n → List (Fin (k + 1)))
    (P : Finset (List (Fin (k + 1))))
    (hI : ∀ i, ∃ α ∈ P, α <+: dp x i) (a : List (Fin (k + 1)))
    (hfin : ¬ IsFinished x a) :
    ∀ i, ∃ α ∈ split x a P, α <+: dp x i := by
  intro i
  obtain ⟨α, hα, hpre⟩ := hI i
  by_cases hea : α = a
  · subst hea
    have hne : α ≠ dp x i := fun h => hfin ⟨i, h⟩
    obtain ⟨u, hu⟩ := pt2076_proper_prefix_extend α (dp x i) hpre hne
    refine ⟨α ++ [u], ?_, hu⟩
    unfold split
    exact Finset.mem_union_right _
      (pt2076_mem_children x α u i (hu.trans (pt2076_dp_prefix x i)))
  · refine ⟨α, ?_, hpre⟩
    unfold split
    exact Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hea, hα⟩)

open PaigeTarjan.LexSort in
theorem solution {k n : ℕ} (x : Fin n → List (Fin (k + 1))) (hn : 0 < n)
    (hx : EndMarked x) (K : ℕ) (Ps : Fin (K + 1) → Finset (List (Fin (k + 1))))
    (hrun : IsRun x K Ps) (j : Fin (K + 1)) :
    (∀ β, IsFinished x β → ∃ α ∈ Ps j, blk x β ⊆ blk x α) ∧
    (∀ β, IsFinished x β → ∃ α ∈ Ps j, α <+: β) := by
  obtain ⟨h0, hstep⟩ := hrun
  have key : ∀ m : ℕ, ∀ hm : m < K + 1, ∀ i, ∃ α ∈ Ps ⟨m, hm⟩, α <+: dp x i := by
    intro m
    induction m with
    | zero =>
      intro hm i
      have : (⟨0, hm⟩ : Fin (K + 1)) = 0 := rfl
      rw [this, h0]
      exact ⟨[], Finset.mem_singleton_self _, List.nil_prefix⟩
    | succ m ih =>
      intro hm
      have hmK : m < K := by omega
      obtain ⟨a, ha, hfin, hP'⟩ := hstep ⟨m, hmK⟩
      have e1 : (Fin.castSucc (⟨m, hmK⟩ : Fin K)) = ⟨m, by omega⟩ := rfl
      have e2 : (Fin.succ (⟨m, hmK⟩ : Fin K)) = ⟨m + 1, hm⟩ := rfl
      rw [e1] at hP'
      rw [e2] at hP'
      rw [hP']
      exact pt2076_step x _ (ih (by omega)) a hfin
  have hj : ∀ β, IsFinished x β → ∃ α ∈ Ps j, α <+: β := by
    rintro β ⟨i, rfl⟩
    exact key j.1 j.2 i
  refine ⟨?_, hj⟩
  intro β hβ
  obtain ⟨α, hα, hpre⟩ := hj β hβ
  refine ⟨α, hα, ?_⟩
  intro t ht
  unfold blk at ht ⊢
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
  exact hpre.trans ht
