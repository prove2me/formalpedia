-- Prove2me | solution 1 for PipelineInterv.Welfare.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:27:44.442549+00:00
-- url     : https://prove2.me/submissions/92d2c7ce-90a1-4b16-a2e2-693fe509fb26

import Mathlib
import Definitions.Def_PipelineInterv_Welfare_Model
set_option autoImplicit false
open Matrix PipelineInterv.Welfare

theorem solution {w : ℕ} (M : Matrix (Fin w) (Fin w) ℝ) (hM : M ∈ colStochastic ℝ (Fin w))
    (D D' : Fin w → ℝ) (hD : IsDist D) (hD' : IsDist D') :
    l1 (M *ᵥ D - M *ᵥ D') ≤ l1 (D - D') := by
  rw [mem_colStochastic] at hM
  obtain ⟨hM0, hM1⟩ := hM
  have hcol : ∀ j, ∑ i, M i j = 1 := fun j => by
    have := congrFun hM1 j
    simpa [Matrix.vecMul, dotProduct] using this
  unfold l1
  have h1 : ∀ i, |(M *ᵥ D - M *ᵥ D') i| ≤ ∑ j, M i j * |D j - D' j| := by
    intro i
    have : (M *ᵥ D - M *ᵥ D') i = ∑ j, M i j * (D j - D' j) := by
      simp [Matrix.mulVec, dotProduct, mul_sub, Finset.sum_sub_distrib]
    rw [this]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    apply Finset.sum_le_sum
    intro j _
    rw [abs_mul, abs_of_nonneg (hM0 i j)]
  calc ∑ i, |(M *ᵥ D - M *ᵥ D') i| ≤ ∑ i, ∑ j, M i j * |D j - D' j| :=
        Finset.sum_le_sum (fun i _ => h1 i)
    _ = ∑ j, (∑ i, M i j) * |D j - D' j| := by
        simp_rw [Finset.sum_mul]; exact Finset.sum_comm
    _ = ∑ j, |D j - D' j| := by simp [hcol]
    _ = ∑ i, |(D - D') i| := rfl
