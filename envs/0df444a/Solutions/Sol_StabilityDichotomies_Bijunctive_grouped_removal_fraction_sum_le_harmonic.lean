-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.grouped_removal_fraction_sum_le_harmonic
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:54:51.814838+00:00
-- url     : https://prove2.me/submissions/e3e9846c-a8e3-4880-b0aa-b3d765cbe65d

import Theorems.Thm_StabilityDichotomies_Bijunctive_harmonic_gap_ge_removed_fraction
noncomputable section
open scoped Classical BigOperators
open StabilityDichotomies.Bijunctive

theorem solution (k : ℕ) (m : ℕ → ℕ)
    (hmono : ∀ i < k, m (i+1) ≤ m i) :
    (∑ i ∈ Finset.range k, ((m i - m (i+1) : ℕ) : ℝ) / m i) ≤ (harmonic (m 0) : ℝ) := by
  have hsum : (∑ i ∈ Finset.range k, ((m i - m (i+1) : ℕ) : ℝ) / m i) ≤
      ∑ i ∈ Finset.range k, ((harmonic (m i) : ℝ) - harmonic (m (i+1))) := by
    apply Finset.sum_le_sum
    intro i hi
    exact harmonic_gap_ge_removed_fraction (m (i+1)) (m i) (hmono i (Finset.mem_range.mp hi))
  rw [Finset.sum_range_sub'] at hsum
  have hnon : 0 ≤ (harmonic (m k) : ℝ) := by
    simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    positivity
  linarith
