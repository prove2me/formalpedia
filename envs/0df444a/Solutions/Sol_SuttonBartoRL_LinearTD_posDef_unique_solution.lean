-- Prove2me | solution 1 for SuttonBartoRL.LinearTD.posDef_unique_solution
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T11:59:39.954211+00:00
-- url     : https://prove2.me/submissions/04f4758a-3775-4610-a633-e5dd946f371a

import Mathlib
import Definitions.Def_SuttonBartoRL_LinearTD_MDP
import Definitions.Def_SuttonBartoRL_LinearTD_LinearTD

open Matrix SuttonBartoRL.LinearTD in
theorem solution {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (b : Fin d → ℝ)
    (hA : IsPosDefNonsym A) :
    IsUnit A.det ∧ A *ᵥ (A⁻¹ *ᵥ b) = b ∧ ∀ w : Fin d → ℝ, A *ᵥ w = b → w = A⁻¹ *ᵥ b := by
  have hdet : A.det ≠ 0 := by
    intro h
    obtain ⟨v, hv, hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
    have := hA v hv
    rw [hAv, dotProduct_zero] at this
    exact lt_irrefl _ this
  have hu : IsUnit A.det := isUnit_iff_ne_zero.mpr hdet
  refine ⟨hu, ?_, ?_⟩
  · rw [mulVec_mulVec, mul_nonsing_inv _ hu, one_mulVec]
  · intro w hw
    rw [← hw, mulVec_mulVec, nonsing_inv_mul _ hu, one_mulVec]

#print axioms solution
