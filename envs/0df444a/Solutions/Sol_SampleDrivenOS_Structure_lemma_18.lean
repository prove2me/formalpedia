-- Prove2me | solution 1 for SampleDrivenOS.Structure.lemma_18
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T22:47:42.930915+00:00
-- url     : https://prove2.me/submissions/5710c5b0-2197-4467-865b-ae814f354138

import Mathlib
import Definitions.Def_SampleDrivenOS_Structure_Setting

open MeasureTheory Set

namespace SDOSL18
open SampleDrivenOS.Structure

/-- Adding the top index to the negative-binomial sum (rank `a+1`, horizon `a+1+m`). -/
lemma nb_succ (a m : ℕ) (t : ℝ) :
    nbTerm (a + 1 + m + 1) (a + 1) t =
      nbTerm (a + 1 + m) (a + 1) t + ((a + 1 + m).choose a : ℝ) * (1 - t) ^ (m + 1) * t ^ (a + 1) := by
  unfold nbTerm
  rw [Finset.sum_Icc_succ_top (by omega)]
  congr 1
  have h1 : a + 1 + m + 1 - 1 = a + 1 + m := by omega
  have h2 : a + 1 - 1 = a := by omega
  have h3 : a + 1 + m + 1 - (a + 1) = m + 1 := by omega
  rw [h1, h2, h3]

lemma nb_succ2 (a m : ℕ) (t : ℝ) :
    nbTerm (a + 1 + m + 1) (a + 2) t =
      nbTerm (a + 1 + m) (a + 2) t + ((a + 1 + m).choose (a + 1) : ℝ) * (1 - t) ^ m * t ^ (a + 2) := by
  unfold nbTerm
  rw [Finset.sum_Icc_succ_top (by omega)]
  congr 1
  have h1 : a + 1 + m + 1 - 1 = a + 1 + m := by omega
  have h2 : a + 2 - 1 = a + 1 := by omega
  have h3 : a + 1 + m + 1 - (a + 2) = m := by omega
  rw [h1, h2, h3]

/-- The difference of consecutive ranks is the binomial probability. -/
lemma nb_diff (a m : ℕ) (t : ℝ) :
    nbTerm (a + 1 + m) (a + 1) t - nbTerm (a + 1 + m) (a + 2) t =
      ((a + 1 + m).choose (a + 1) : ℝ) * t ^ (a + 1) * (1 - t) ^ m := by
  induction m with
  | zero =>
    unfold nbTerm
    have hE : Finset.Icc (a + 2) (a + 1 + 0) = ∅ := by
      ext x; simp
    have hS : Finset.Icc (a + 1) (a + 1 + 0) = {a + 1} := by
      ext x; simp
    rw [hE, hS]
    simp
  | succ m ih =>
    have e1 := nb_succ a m t
    have e2 := nb_succ2 a m t
    have e3 : a + 1 + (m + 1) = a + 1 + m + 1 := by omega
    rw [e3, e1, e2]
    have hc : ((a + 1 + m + 1).choose (a + 1) : ℝ) =
        ((a + 1 + m).choose a : ℝ) + ((a + 1 + m).choose (a + 1) : ℝ) := by
      rw [Nat.choose_succ_succ]; push_cast; ring
    rw [hc]
    have : nbTerm (a + 1 + m) (a + 1) t + ((a + 1 + m).choose a : ℝ) * (1 - t) ^ (m + 1) * t ^ (a + 1) -
        (nbTerm (a + 1 + m) (a + 2) t + ((a + 1 + m).choose (a + 1) : ℝ) * (1 - t) ^ m * t ^ (a + 2)) =
        (nbTerm (a + 1 + m) (a + 1) t - nbTerm (a + 1 + m) (a + 2) t) +
        ((a + 1 + m).choose a : ℝ) * (1 - t) ^ (m + 1) * t ^ (a + 1) -
        ((a + 1 + m).choose (a + 1) : ℝ) * (1 - t) ^ m * t ^ (a + 2) := by ring
    rw [this, ih]
    ring

lemma nb_step (k ℓ : ℕ) (hℓ : 1 ≤ ℓ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    nbTerm k (ℓ + 1) t ≤ nbTerm k ℓ t := by
  obtain ⟨a, rfl⟩ : ∃ a, ℓ = a + 1 := ⟨ℓ - 1, by omega⟩
  by_cases hk : a + 1 ≤ k
  · obtain ⟨m, rfl⟩ : ∃ m, k = a + 1 + m := ⟨k - (a + 1), by omega⟩
    have := nb_diff a m t
    have h0 : 0 ≤ ((a + 1 + m).choose (a + 1) : ℝ) * t ^ (a + 1) * (1 - t) ^ m := by
      have : 0 ≤ 1 - t := by linarith [ht.2]
      have : 0 ≤ t := ht.1
      positivity
    have e : a + 1 + 1 = a + 2 := by omega
    rw [e]
    linarith
  · have h1 : Finset.Icc (a + 1 + 1) k = ∅ := by ext x; simp; omega
    have h2 : Finset.Icc (a + 1) k = ∅ := by ext x; simp; omega
    unfold nbTerm
    rw [h1, h2]
    simp

end SDOSL18

open SampleDrivenOS.Structure in
theorem solution (k : ℕ) (hk : 1 ≤ k) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    AntitoneOn (fun ℓ : ℕ => nbTerm k ℓ t) (Ici 1) := by
  intro ℓ hℓ ℓ' hℓ' hle
  simp only [mem_Ici] at hℓ hℓ'
  induction ℓ', hle using Nat.le_induction with
  | base => exact le_rfl
  | succ n hn ih =>
    exact le_trans (SDOSL18.nb_step k n (le_trans hℓ hn) t ht) (ih (le_trans hℓ hn))
