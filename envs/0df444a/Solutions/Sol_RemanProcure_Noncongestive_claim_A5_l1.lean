-- Prove2me | solution 1 for RemanProcure.Noncongestive.claim_A5_l1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T21:17:16.648129+00:00
-- url     : https://prove2.me/submissions/a022cfa2-538d-4c33-bac6-af8bde13bb53

import Mathlib
import Definitions.Def_RemanProcure_Noncongestive_Model
import Theorems.Thm_RemanProcure_Noncongestive_lemma_1_vstar

open RemanProcure.Noncongestive

theorem solution {K : ℕ} (P : Params K) (hP : Standing P) : ∀ (x : Fin K → ℕ) (q : Fin K), acqGap P x ≤ acqGap P (x + e q) := by
  intro x q
  have hV := lemma_1_vstar P hP
  obtain ⟨-, -, -, -, hA5, -⟩ := hV
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
  have h := hA5 x l q (hmin q)
  rw [key, key] at h
  unfold acqGap
  linarith
