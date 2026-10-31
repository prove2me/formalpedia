-- Prove2me | solution 1 for RemanProcure.Noncongestive.claim_A6_l1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T21:17:17.439491+00:00
-- url     : https://prove2.me/submissions/7f9d9beb-fbc5-4f3b-a396-f07266baf067

import Mathlib
import Definitions.Def_RemanProcure_Noncongestive_Model
import Theorems.Thm_RemanProcure_Noncongestive_lemma_1_vstar

open RemanProcure.Noncongestive

theorem solution {K : ℕ} (P : Params K) (hP : Standing P) : ∀ (x : Fin K → ℕ) (q w : Fin K), q < w → acqGap P (x + e w) ≤ acqGap P (x + e q) := by
  intro x q w hqw
  have hV := lemma_1_vstar P hP
  obtain ⟨-, -, -, -, -, hA6⟩ := hV
  have hK : 0 < K := hP.1
  set l : Fin K := ⟨0, hK⟩ with hl
  have hmin : ∀ i : Fin K, l ≤ i := fun i => by
    simp [hl, Fin.le_def]
  have key : ∀ y : Fin K → ℕ,
      (∑ i ∈ Finset.univ.filter (· ≤ l), P.p i * vstar P (y + e l))
        + (∑ i ∈ Finset.univ.filter (l < ·), P.p i * vstar P (y + e i))
        = ∑ i, P.p i * vstar P (y + e i) := by
    intro y
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ≤ l)]
    congr 1
    · apply Finset.sum_congr rfl
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      have : i = l := le_antisymm hi (hmin i)
      rw [this]
    · apply Finset.sum_congr
      · ext i; simp [not_le]
      · intro i _; rfl
  have h := hA6 x l q w (hmin q) hqw
  rw [key, key] at h
  unfold acqGap
  linarith
