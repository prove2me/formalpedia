-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.grouped_winner_changes_inject_into_suffix_records
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:54:37.429717+00:00
-- url     : https://prove2.me/submissions/0f1d49ee-236a-4f13-9beb-7f5ede06cd43

import Mathlib
noncomputable section
open scoped Classical BigOperators

theorem solution {α : Type} [DecidableEq α]
    (n k : ℕ) (score : Fin n → ℝ) (hinj : Function.Injective score)
    (label : Fin n → α) (cut : Fin (k+1) → ℕ) (hcut : Monotone cut)
    (before after : Fin k → Fin n)
    (hbefore : ∀ i, cut i.castSucc ≤ (before i).val)
    (hafter : ∀ i, cut i.succ ≤ (after i).val)
    (hmaxBefore : ∀ i j, cut i.castSucc ≤ j.val → score j ≤ score (before i))
    (hmaxAfter : ∀ i j, cut i.succ ≤ j.val → score j ≤ score (after i)) :
    (Finset.univ.filter (fun i : Fin k => label (before i) ≠ label (after i))).card ≤
      (Finset.univ.filter (fun i : Fin n => ∀ j : Fin n, i.val < j.val → score j < score i)).card := by
  classical
  let changes : Finset (Fin k) := Finset.univ.filter (fun i => label (before i) ≠ label (after i))
  let records : Finset (Fin n) := Finset.univ.filter (fun i => ∀ j : Fin n, i.val < j.val → score j < score i)
  have hremoved (i : Fin k) (hi : i ∈ changes) : (before i).val < cut i.succ := by
    have hchange : label (before i) ≠ label (after i) := (Finset.mem_filter.mp hi).2
    have hne : before i ≠ after i := by intro h; rw [h] at hchange; exact hchange rfl
    by_contra h
    have hsurv : cut i.succ ≤ (before i).val := by omega
    have hmono : cut i.castSucc ≤ cut i.succ := hcut (le_of_lt Fin.castSucc_lt_succ)
    have h1 := hmaxBefore i (after i) (le_trans hmono (hafter i))
    have h2 := hmaxAfter i (before i) hsurv
    exact hne (hinj (le_antisymm h2 h1))
  apply Finset.card_le_card_of_injOn before
  · intro i hi
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    intro j hj
    have hle := hmaxBefore i j (by have := hbefore i; omega)
    have hne : j ≠ before i := by intro he; have := congrArg Fin.val he; omega
    exact lt_of_le_of_ne hle (fun he => hne (hinj he))
  · intro i hi j hj heq
    by_contra hne
    rcases lt_or_gt_of_ne hne with hij | hji
    · have hcuts : cut i.succ ≤ cut j.castSucc := by
        apply hcut
        apply Fin.le_def.mpr
        simp only [Fin.val_succ, Fin.val_castSucc]
        omega
      have hlt := hremoved i hi
      have hjb := hbefore j
      have hv := congrArg Fin.val heq
      omega
    · have hcuts : cut j.succ ≤ cut i.castSucc := by
        apply hcut
        apply Fin.le_def.mpr
        simp only [Fin.val_succ, Fin.val_castSucc]
        omega
      have hlt := hremoved j hj
      have hib := hbefore i
      have hv := congrArg Fin.val heq
      omega
