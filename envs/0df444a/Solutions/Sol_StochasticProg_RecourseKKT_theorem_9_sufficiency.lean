-- Prove2me | solution 1 for StochasticProg.RecourseKKT.theorem_9_sufficiency
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-05T00:44:07.113449+00:00
-- url     : https://prove2.me/submissions/fe543e73-8282-45ee-aa0e-56abc4f8480c

import Mathlib
import Definitions.Def_StochasticProg_RecourseKKT_RecourseData
import Definitions.Def_StochasticProg_RecourseKKT_expectedRecourse
import Definitions.Def_StochasticProg_RecourseKKT_firstStageSet
import Definitions.Def_StochasticProg_RecourseKKT_IsOptimalDEP
import Definitions.Def_StochasticProg_RecourseKKT_subdifferential

set_option autoImplicit false

open MeasureTheory Matrix StochasticProg.RecourseKKT in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {n1 m1 n2 m2 : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (pb : RecourseData Ω n1 m1 n2 m2)
    (xs : Fin n1 → ℝ) (hxs : xs ∈ firstStageSet pb.A pb.b)
    (hkkt : ∃ (lam : Fin m1 → ℝ) (mu : Fin n1 → ℝ), 0 ≤ mu ∧ mu ⬝ᵥ xs = 0 ∧
          -pb.c + pb.Aᵀ *ᵥ lam + mu ∈ subdifferential (expectedRecourse P pb) xs) :
    IsOptimalDEP P pb xs := by
  obtain ⟨lam, mu, hmu, hmux, r, hr, hsub⟩ := hkkt
  refine ⟨hxs, fun x hx => ?_⟩
  have key := hsub x
  have hAx : pb.A *ᵥ (x - xs) = 0 := by rw [Matrix.mulVec_sub, hx.1, hxs.1, sub_self]
  have hlam : (pb.Aᵀ *ᵥ lam) ⬝ᵥ (x - xs) = 0 := by
    rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, hAx, dotProduct_zero]
  have hmu0 : 0 ≤ mu ⬝ᵥ x := dotProduct_nonneg_of_nonneg hmu hx.2
  have hineq : pb.c ⬝ᵥ xs - pb.c ⬝ᵥ x ≤ (-pb.c + pb.Aᵀ *ᵥ lam + mu) ⬝ᵥ (x - xs) := by
    rw [add_dotProduct, add_dotProduct, hlam]
    simp only [dotProduct_sub, neg_dotProduct, hmux]
    linarith
  unfold depObjective
  rw [hr]
  calc ((pb.c ⬝ᵥ xs : ℝ) : EReal) + (r : EReal)
      = ((pb.c ⬝ᵥ x : ℝ) : EReal) + ((r + (pb.c ⬝ᵥ xs - pb.c ⬝ᵥ x) : ℝ) : EReal) := by
        rw [← EReal.coe_add, ← EReal.coe_add]; congr 1; ring
    _ ≤ ((pb.c ⬝ᵥ x : ℝ) : EReal) + ((r + (-pb.c + pb.Aᵀ *ᵥ lam + mu) ⬝ᵥ (x - xs) : ℝ) : EReal) := by
        exact add_le_add le_rfl (EReal.coe_le_coe_iff.mpr (by linarith))
    _ ≤ ((pb.c ⬝ᵥ x : ℝ) : EReal) + expectedRecourse P pb x := add_le_add le_rfl key
