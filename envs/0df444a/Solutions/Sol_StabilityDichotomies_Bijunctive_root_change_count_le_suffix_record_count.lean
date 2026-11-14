-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.root_change_count_le_suffix_record_count
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:54:36.469442+00:00
-- url     : https://prove2.me/submissions/91d751db-17e2-4f50-a37d-c1e9d561c8d7

import Mathlib
noncomputable section
open scoped Classical BigOperators

private theorem changed_winner_implies_suffix_record {α : Type} (n : ℕ)
    (score : Fin (n+1) → ℝ) (hinj : Function.Injective score)
    (label : Fin (n+1) → α) (i : Fin n) (before after : Fin (n+1))
    (hbefore : i.val ≤ before.val) (hafter : i.val + 1 ≤ after.val)
    (hmaxBefore : ∀ k : Fin (n+1), i.val ≤ k.val → score k ≤ score before)
    (hmaxAfter : ∀ k : Fin (n+1), i.val + 1 ≤ k.val → score k ≤ score after)
    (hchange : label before ≠ label after) :
    ∀ k : Fin (n+1), i.val < k.val → score k < score (Fin.castSucc i) := by
  have hne : before ≠ after := by intro h; subst after; exact hchange rfl
  have hb : before.val = i.val := by
    by_contra hh
    have hs : i.val + 1 ≤ before.val := by omega
    have h1 := hmaxBefore after (by omega)
    have h2 := hmaxAfter before hs
    have he : score before = score after := le_antisymm h2 h1
    exact hne (hinj he)
  have hbeforeeq : before = Fin.castSucc i := by apply Fin.ext; simpa using hb
  intro k hk
  have hk0 : i.val ≤ k.val := by omega
  have hle := hmaxBefore k hk0
  have hkne : k ≠ before := by intro h; have := congrArg Fin.val h; omega
  have hscore : score k ≠ score before := fun h => hkne (hinj h)
  rw [← hbeforeeq]
  exact lt_of_le_of_ne hle hscore

theorem solution {α : Type} [DecidableEq α] (n : ℕ)
    (score : Fin (n+1) → ℝ) (hinj : Function.Injective score)
    (label : Fin (n+1) → α) (before after : Fin n → Fin (n+1))
    (hbefore : ∀ i, i.val ≤ (before i).val) (hafter : ∀ i, i.val + 1 ≤ (after i).val)
    (hmaxBefore : ∀ i k, i.val ≤ k.val → score k ≤ score (before i))
    (hmaxAfter : ∀ i k, i.val + 1 ≤ k.val → score k ≤ score (after i)) :
    (∑ i : Fin n, if label (before i) ≠ label (after i) then (1 : ℕ) else 0) ≤
      ∑ i : Fin n, if ∀ k : Fin (n+1), i.val < k.val → score k < score (Fin.castSucc i)
        then (1 : ℕ) else 0 := by
  apply Finset.sum_le_sum
  intro i hi
  by_cases h : label (before i) ≠ label (after i)
  · have hh := changed_winner_implies_suffix_record n score hinj label i (before i) (after i)
      (hbefore i) (hafter i) (hmaxBefore i) (hmaxAfter i) h
    rw [if_pos h, if_pos hh]
  · simp [h]
