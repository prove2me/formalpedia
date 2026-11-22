-- Prove2me | solution 1 for SeqPostedPricing.PartitionSPM.lemma_20_equal_price_revenue
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-21T06:17:56.043358+00:00
-- url     : https://prove2.me/submissions/1d8e8ece-c094-45d4-9105-8ca259e15d15

import Mathlib

theorem solution {n : ℕ} (c p q : Fin n → ℝ) (pbar : ℝ)
    (hc : Antitone c) (hp : Antitone p) (hq : ∀ i, 0 ≤ q i)
    (h2 : ∑ i, p i * q i = pbar * ∑ i, q i) :
    ∑ i, c i * (pbar * q i) ≤ ∑ i, c i * p i * q i := by
  classical
  have hnn : 0 ≤ ∑ i : Fin n, ∑ j : Fin n, q i * q j * (c i - c j) * (p i - p j) := by
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    have hqij : 0 ≤ q i * q j := mul_nonneg (hq i) (hq j)
    rcases le_total i j with hij | hij
    · have hc' : 0 ≤ c i - c j := by linarith [hc hij]
      have hp' : 0 ≤ p i - p j := by linarith [hp hij]
      have h1 : 0 ≤ (c i - c j) * (p i - p j) := mul_nonneg hc' hp'
      nlinarith [hqij, h1]
    · have hc' : 0 ≤ c j - c i := by linarith [hc hij]
      have hp' : 0 ≤ p j - p i := by linarith [hp hij]
      have h1 : 0 ≤ (c j - c i) * (p j - p i) := mul_nonneg hc' hp'
      nlinarith [hqij, h1]
  have expand : ∑ i : Fin n, ∑ j : Fin n, q i * q j * (c i - c j) * (p i - p j)
      = 2 * ((∑ i, q i) * (∑ i, c i * p i * q i) - (∑ i, c i * q i) * (∑ i, p i * q i)) := by
    have hpt : ∀ i j : Fin n, q i * q j * (c i - c j) * (p i - p j) =
        (c i * p i * q i) * q j - (c i * q i) * (p j * q j) - (p i * q i) * (c j * q j) +
          q i * (c j * p j * q j) := by
      intro i j; ring
    simp only [hpt, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [← Finset.sum_mul_sum, ← Finset.sum_mul_sum, ← Finset.sum_mul_sum, ← Finset.sum_mul_sum]
    ring
  have hcheb : (∑ i, c i * q i) * (∑ i, p i * q i) ≤ (∑ i, q i) * (∑ i, c i * p i * q i) := by
    nlinarith [hnn, expand]
  have e1 : ∑ i, c i * (pbar * q i) = pbar * ∑ i, c i * q i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [e1]
  by_cases hD : (∑ i, q i) = 0
  · have hq0 : ∀ i, q i = 0 := by
      intro i
      have h1 : q i ≤ ∑ j, q j :=
        Finset.single_le_sum (f := q) (fun j _ => hq j) (Finset.mem_univ i)
      rw [hD] at h1
      linarith [hq i]
    simp [hq0]
  · have hDpos : 0 < ∑ i, q i :=
      lt_of_le_of_ne (Finset.sum_nonneg (fun i _ => hq i)) (Ne.symm hD)
    have h3 : ((∑ i, c i * q i) * pbar) * (∑ i, q i) ≤
        (∑ i, c i * p i * q i) * (∑ i, q i) := by
      calc ((∑ i, c i * q i) * pbar) * (∑ i, q i) = (∑ i, c i * q i) * (∑ i, p i * q i) := by
            rw [h2]; ring
        _ ≤ (∑ i, q i) * (∑ i, c i * p i * q i) := hcheb
        _ = (∑ i, c i * p i * q i) * (∑ i, q i) := by ring
    have h4 : (∑ i, c i * q i) * pbar ≤ ∑ i, c i * p i * q i :=
      le_of_mul_le_mul_right h3 hDpos
    calc pbar * ∑ i, c i * q i = (∑ i, c i * q i) * pbar := by ring
      _ ≤ ∑ i, c i * p i * q i := h4
