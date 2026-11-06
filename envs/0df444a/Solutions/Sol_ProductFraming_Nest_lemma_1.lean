-- Prove2me | solution 1 for ProductFraming.Nest.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T06:50:49.307377+00:00
-- url     : https://prove2.me/submissions/e6d48341-bada-4517-83d2-c7fc8a3b4226

import Mathlib
import Definitions.Def_ProductFraming_Nest_Model

open Finset ProductFraming.Nest

theorem solution (n : ℕ) (r : Fin n → ℝ) (hr : ∀ i, 0 ≤ r i) (P : Fin n → Finset (Fin n) → ℝ)
    (hP : IsChoiceModel P) (hA1 : SatisfiesA1 P) (S : Finset (Fin n)) (hS : 2 ≤ S.card) :
    ∃ i ∈ S, R r P S / (S.card : ℝ) ≤ R r P (S.erase i) / ((S.card : ℝ) - 1) := by
  have hne : S.Nonempty := by
    rw [← Finset.card_pos]; omega
  have hc : (2 : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast hS
  have hc0 : (0 : ℝ) < S.card := by linarith
  have hc1 : (0 : ℝ) < (S.card : ℝ) - 1 := by linarith
  -- removing `i` does not lower the purchase probabilities of the others (A1)
  have hrem : ∀ i ∈ S, R r P S - r i * P i S ≤ R r P (S.erase i) := by
    intro i hi
    unfold R
    rw [← Finset.sum_erase_eq_sub hi]
    apply sum_le_sum
    intro k hk
    exact mul_le_mul_of_nonneg_left (hA1 (S.erase i) S k (erase_subset i S) hk) (hr k)
  have hsum : ∑ _i ∈ S, ((S.card : ℝ) - 1) * R r P S / S.card ≤ ∑ i ∈ S, R r P (S.erase i) := by
    have h1 : ∑ i ∈ S, (R r P S - r i * P i S) ≤ ∑ i ∈ S, R r P (S.erase i) := sum_le_sum hrem
    have h2 : ∑ i ∈ S, (R r P S - r i * P i S) = ((S.card : ℝ) - 1) * R r P S := by
      rw [sum_sub_distrib, sum_const, nsmul_eq_mul]
      unfold R; ring
    have h3 : ∑ _i ∈ S, ((S.card : ℝ) - 1) * R r P S / S.card = ((S.card : ℝ) - 1) * R r P S := by
      rw [sum_const, nsmul_eq_mul]; field_simp
    linarith
  obtain ⟨i, hi, hle⟩ := Finset.exists_le_of_sum_le hne hsum
  refine ⟨i, hi, ?_⟩
  rw [le_div_iff₀ hc1]
  calc R r P S / S.card * ((S.card : ℝ) - 1) = ((S.card : ℝ) - 1) * R r P S / S.card := by ring
    _ ≤ _ := hle
