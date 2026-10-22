-- Prove2me | solution 1 for TradeCreditIns.Cancelable.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T11:08:14.100038+00:00
-- url     : https://prove2.me/submissions/e855387f-dc20-49a9-8d25-d921a49287d6

import Mathlib
import Definitions.Def_TradeCreditIns_Cancelable_Model

open TradeCreditIns.Cancelable

theorem solution (P : Params) (hS : P.Standing)
    (hA1 : Assumption1 P) :
    firstBest P = (1 - P.βbar) * P.r + max (φ P - P.c) 0 ∧
    firstBest P - noInsurance P =
      min (P.βbar * L P 0) ((1 - P.βbar) * P.r - P.r0) +
        max (φ P - P.c) 0 := by
  obtain ⟨hθ, hsum, -, -, -, -, -, -, hbar, -, -⟩ := hS
  classical
  let g : (Fin 3 → Bool) → ℝ := fun s =>
    (∑ i, P.θ i * (if s i then (1 - P.β i) * P.r else P.r0)) - P.c
  have hM : ∑ i, P.θ i * max ((1 - P.β i) * P.r) P.r0 =
      (1 - P.βbar) * P.r + φ P := by
    have e : ∀ i, P.θ i * max ((1 - P.β i) * P.r) P.r0 =
        P.θ i * ((1 - P.β i) * P.r) +
          P.θ i * max (P.r0 - (1 - P.β i) * P.r) 0 := by
      intro i
      rw [← mul_add]; congr 1
      rcases le_total ((1 - P.β i) * P.r) P.r0 with h | h
      · rw [max_eq_right h, max_eq_left (by linarith)]; ring
      · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    simp only [e, Finset.sum_add_distrib]
    unfold φ Params.βbar
    rw [Fin.sum_univ_three] at hsum
    simp only [Fin.sum_univ_three]
    linear_combination P.r * hsum
  have hsup : Finset.univ.sup' Finset.univ_nonempty g =
      (1 - P.βbar) * P.r + φ P - P.c := by
    apply le_antisymm
    · apply Finset.sup'_le
      intro s _
      simp only [g]
      rw [← hM]
      have : ∑ i, P.θ i * (if s i then (1 - P.β i) * P.r else P.r0) ≤
          ∑ i, P.θ i * max ((1 - P.β i) * P.r) P.r0 := by
        apply Finset.sum_le_sum
        intro i _
        apply mul_le_mul_of_nonneg_left _ (hθ i)
        split_ifs
        · exact le_max_left _ _
        · exact le_max_right _ _
      linarith
    · refine Finset.le_sup'_of_le _
        (Finset.mem_univ (fun i : Fin 3 => decide (P.r0 ≤ (1 - P.β i) * P.r))) ?_
      simp only [g]
      rw [← hM]
      have : ∑ i, P.θ i * (if decide (P.r0 ≤ (1 - P.β i) * P.r) = true
            then (1 - P.β i) * P.r else P.r0) =
          ∑ i, P.θ i * max ((1 - P.β i) * P.r) P.r0 := by
        apply Finset.sum_congr rfl
        intro i _
        congr 1
        by_cases h : P.r0 ≤ (1 - P.β i) * P.r
        · simp [h]
        · simp only [h, decide_false]
          rw [max_eq_right (by linarith)]; simp
      linarith
  have hFB : firstBest P = (1 - P.βbar) * P.r + max (φ P - P.c) 0 := by
    unfold firstBest
    change max (max ((1 - P.βbar) * P.r) P.r0)
      (Finset.univ.sup' Finset.univ_nonempty g) = _
    rw [hsup, max_eq_left hbar.le]
    rcases le_total (φ P - P.c) 0 with h | h
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  refine ⟨hFB, ?_⟩
  rw [hFB]
  unfold noInsurance
  rcases le_total ((1 - P.βbar) * P.r - P.βbar * L P 0) P.r0 with h | h
  · rw [max_eq_right h, min_eq_right (by linarith)]; ring
  · rw [max_eq_left h, min_eq_left (by linarith)]; ring
