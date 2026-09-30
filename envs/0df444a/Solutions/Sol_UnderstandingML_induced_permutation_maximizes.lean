-- Prove2me | solution 1 for UnderstandingML.induced_permutation_maximizes
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-26T06:40:53.924251+00:00
-- url     : https://prove2.me/submissions/1a0a0a40-9718-434c-87d5-86df16a82e8d

import Definitions.Def_UnderstandingML_Multiclass

open MeasureTheory
open scoped InnerProductSpace
open UnderstandingML

theorem solution {r : ℕ} (y : Fin r → ℝ) (σ : Equiv.Perm (Fin r))
    (hσ : Monovary (fun i ↦ ((σ i : ℕ) : ℝ)) y) (τ : Equiv.Perm (Fin r)) :
    ∑ i, ((τ i : ℕ) : ℝ) * y i ≤ ∑ i, ((σ i : ℕ) : ℝ) * y i := by
  have h := hσ.sum_comp_perm_mul_le_sum_mul (σ := σ⁻¹ * τ)
  simpa [Equiv.Perm.mul_apply] using h
