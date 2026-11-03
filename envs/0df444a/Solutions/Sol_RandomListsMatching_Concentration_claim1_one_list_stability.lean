-- Prove2me | solution 1 for RandomListsMatching.Concentration.claim1_one_list_stability
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T20:04:25.640296+00:00
-- url     : https://prove2.me/submissions/8cdd1d37-9985-41b5-b75e-16bc1f174a26

import Mathlib
import Definitions.Def_RandomListsMatching_Concentration_Setting

open RandomListsMatching.Concentration

private def DiffByAtMostOneInsert {A : Type} [DecidableEq A] (W W' : Finset A) : Prop :=
  W' = W ∨ ∃ x, W' = insert x W

private lemma greedyStep_nil {A : Type} [DecidableEq A] (W : Finset A) :
    greedyStep W [] = W := rfl

private lemma diffByAtMostOneInsert_greedyStep_self {A : Type} [DecidableEq A]
    (W : Finset A) (l : List A) :
    DiffByAtMostOneInsert W (greedyStep W l) := by
  unfold greedyStep DiffByAtMostOneInsert
  cases l.find? (fun a => decide (a ∉ W)) with
  | none => left; rfl
  | some a => right; exact ⟨a, rfl⟩

private lemma find_not_mem_insert_of_none {A : Type} [DecidableEq A]
    (W : Finset A) (x : A) (l : List A)
    (h : l.find? (fun a => decide (a ∉ W)) = none) :
    l.find? (fun a => decide (a ∉ insert x W)) = none := by
  rw [List.find?_eq_none] at h ⊢
  intro a ha
  have h1 := h a ha
  simp only [decide_eq_true_eq, not_not] at h1 ⊢
  exact Finset.mem_insert_of_mem h1

private lemma find_not_mem_insert_of_some_ne {A : Type} [DecidableEq A]
    (W : Finset A) (x a : A) (l : List A)
    (h : l.find? (fun b => decide (b ∉ W)) = some a) (hne : a ≠ x) :
    l.find? (fun b => decide (b ∉ insert x W)) = some a := by
  induction l with
  | nil => simp at h
  | cons hd tl ih =>
    rw [List.find?_cons] at h ⊢
    by_cases hmem : hd ∈ W
    · have hd1 : decide (hd ∉ W) = false := decide_eq_false (not_not.mpr hmem)
      have hd2 : decide (hd ∉ insert x W) = false :=
        decide_eq_false (not_not.mpr (Finset.mem_insert_of_mem hmem))
      rw [hd1] at h
      rw [hd2]
      exact ih h
    · have hd1 : decide (hd ∉ W) = true := decide_eq_true hmem
      rw [hd1] at h
      injection h with hhd
      subst hhd
      have hd2 : decide (hd ∉ insert x W) = true :=
        decide_eq_true (by simp [Finset.mem_insert, hne, hmem])
      rw [hd2]

private lemma diffByAtMostOneInsert_greedyStep {A : Type} [DecidableEq A]
    {W W' : Finset A} (h : DiffByAtMostOneInsert W W') (l : List A) :
    DiffByAtMostOneInsert (greedyStep W l) (greedyStep W' l) := by
  rcases h with rfl | ⟨x, rfl⟩
  · left; rfl
  · cases hfind : l.find? (fun a => decide (a ∉ W)) with
    | none =>
      have h1 : greedyStep W l = W := by unfold greedyStep; rw [hfind]
      have h2 : greedyStep (insert x W) l = insert x W := by
        unfold greedyStep; rw [find_not_mem_insert_of_none W x l hfind]
      rw [h1, h2]
      exact Or.inr ⟨x, rfl⟩
    | some a =>
      have h1 : greedyStep W l = insert a W := by unfold greedyStep; rw [hfind]
      by_cases hax : a = x
      · subst hax
        rw [h1]
        exact diffByAtMostOneInsert_greedyStep_self (insert a W) l
      · have h2 : greedyStep (insert x W) l = insert a (insert x W) := by
          unfold greedyStep; rw [find_not_mem_insert_of_some_ne W x a l hfind hax]
        rw [h1, h2]
        exact Or.inr ⟨x, Finset.insert_comm a x W⟩

private lemma matchedAfter_update_eq_of_le {A : Type} [DecidableEq A] {n : ℕ}
    (ls : Fin n → List A) (t : Fin n) (j : ℕ) (hj : j ≤ t.val) :
    matchedAfter (Function.update ls t []) j = matchedAfter ls j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hj_lt : j < t.val := Nat.lt_of_succ_le hj
    have hjn : j < n := Nat.lt_trans hj_lt t.isLt
    have hne : (⟨j, hjn⟩ : Fin n) ≠ t := by
      intro heq
      have : j = t.val := congrArg Fin.val heq
      omega
    simp [matchedAfter, hjn, ih (Nat.le_of_lt hj_lt), Function.update_of_ne hne]

private lemma diffByAtMostOneInsert_matchedAfter_update {A : Type} [DecidableEq A] {n : ℕ}
    (ls : Fin n → List A) (t : Fin n) (j : ℕ) :
    DiffByAtMostOneInsert (matchedAfter (Function.update ls t []) j) (matchedAfter ls j) := by
  induction j with
  | zero => exact Or.inl rfl
  | succ j ih =>
    simp only [matchedAfter]
    split_ifs with hjn
    · by_cases hjt : (⟨j, hjn⟩ : Fin n) = t
      · have hj_le : j ≤ t.val := by
          have : j = t.val := congrArg Fin.val hjt
          omega
        rw [matchedAfter_update_eq_of_le ls t j hj_le, hjt, Function.update_self, greedyStep_nil]
        exact diffByAtMostOneInsert_greedyStep_self (matchedAfter ls j) (ls t)
      · rw [Function.update_of_ne hjt]
        exact diffByAtMostOneInsert_greedyStep ih (ls ⟨j, hjn⟩)
    · exact ih

private lemma algValue_update_bounds {A : Type} [DecidableEq A] {n : ℕ}
    (ls : Fin n → List A) (t : Fin n) :
    algValue (Function.update ls t []) ≤ algValue ls ∧
      algValue ls ≤ algValue (Function.update ls t []) + 1 := by
  unfold algValue
  rcases diffByAtMostOneInsert_matchedAfter_update ls t n with h | ⟨x, h⟩
  · rw [h]
    exact ⟨le_refl _, Nat.le_succ _⟩
  · rw [h]
    exact ⟨Finset.card_le_card (Finset.subset_insert x _), Finset.card_insert_le x _⟩

theorem solution {A : Type} [DecidableEq A] {n : ℕ} (ls ls' : Fin n → List A)
    (t : Fin n) (hdiff : ∀ j, j ≠ t → ls j = ls' j) :
    |(algValue ls : ℤ) - (algValue ls' : ℤ)| ≤ 1 := by
  have hupd : Function.update ls' t [] = Function.update ls t [] := by
    ext j
    by_cases hjt : j = t
    · subst hjt; simp
    · simp [hjt, hdiff j hjt]
  have h1 := algValue_update_bounds ls t
  have h2 := algValue_update_bounds ls' t
  rw [hupd] at h2
  rw [abs_le]
  constructor <;> omega
