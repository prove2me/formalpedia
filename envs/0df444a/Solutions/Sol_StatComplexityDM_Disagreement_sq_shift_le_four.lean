-- Prove2me | solution 1 for StatComplexityDM.Disagreement.sq_shift_le_four
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T05:05:56.088333+00:00
-- url     : https://prove2.me/submissions/b565d5dd-d4ab-4843-8860-9e6961394abd

import Mathlib
import Definitions.Def_StatComplexityDM_Disagreement_Coefficient

set_option autoImplicit false

theorem solution {ι Act : Type*} [Fintype ι] (w : ι → ℝ) (hw : StatComplexityDM.LowerBound.IsDist w)
    (fM : ι → Act → ℝ) (fbar : Act → ℝ) (π : Act) :
    ∑ i, w i * ∑ k, w k * (fM i π - fM k π) ^ 2 ≤ 4 * ∑ i, w i * (fM i π - fbar π) ^ 2 := by
  obtain ⟨h0, h1⟩ := hw
  have key : ∀ i, ∑ k, w k * (fM i π - fM k π) ^ 2 ≤
      2 * (fM i π - fbar π) ^ 2 + 2 * ∑ k, w k * (fM k π - fbar π) ^ 2 := by
    intro i
    calc ∑ k, w k * (fM i π - fM k π) ^ 2
        ≤ ∑ k, w k * (2 * (fM i π - fbar π) ^ 2 + 2 * (fM k π - fbar π) ^ 2) := by
          apply Finset.sum_le_sum
          intro k _
          apply mul_le_mul_of_nonneg_left _ (h0 k)
          nlinarith [sq_nonneg ((fM i π - fbar π) + (fM k π - fbar π))]
      _ = 2 * (fM i π - fbar π) ^ 2 * ∑ k, w k + 2 * ∑ k, w k * (fM k π - fbar π) ^ 2 := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro k _
          ring
      _ = _ := by rw [h1]; ring
  calc ∑ i, w i * ∑ k, w k * (fM i π - fM k π) ^ 2
      ≤ ∑ i, w i * (2 * (fM i π - fbar π) ^ 2 + 2 * ∑ k, w k * (fM k π - fbar π) ^ 2) := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left (key i) (h0 i)
    _ = 4 * ∑ i, w i * (fM i π - fbar π) ^ 2 := by
        have e : ∀ i, w i * (2 * (fM i π - fbar π) ^ 2 + 2 * ∑ k, w k * (fM k π - fbar π) ^ 2)
            = 2 * (w i * (fM i π - fbar π) ^ 2)
              + (2 * ∑ k, w k * (fM k π - fbar π) ^ 2) * w i := by
          intro i; ring
        simp_rw [e]
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, h1]
        ring
