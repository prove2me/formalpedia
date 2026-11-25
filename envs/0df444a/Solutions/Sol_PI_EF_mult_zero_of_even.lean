-- Prove2me | solution 1 for PI.EF.mult_zero_of_even
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:04:00.930207+00:00
-- url     : https://prove2.me/submissions/1821658d-a1fc-49b5-85ed-dc98d690763e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LStructB
import Theorems.Thm_PI_EF_completed_ne_zero_left
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace PI.EF
open Complex Filter Topology Set DirichletCharacter
section prim
variable {N : ℕ}
end prim
variable {N : ℕ} [NeZero N]
private lemma exists_differentiable_Gammaℝ_inv_eq_mul : ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ g 0 ≠ 0 ∧
    ∀ z : ℂ, (Gammaℝ z)⁻¹ = z * g z := by
  refine ⟨fun s => (Real.pi : ℂ) ^ (s / 2) * (1 / 2 * (Complex.Gamma (s / 2 + 1))⁻¹), ?_, ?_, ?_⟩
  · refine Differentiable.mul ?_ ?_
    · exact (differentiable_id.div_const (2 : ℂ)).const_cpow
        (Or.inl (by exact_mod_cast Real.pi_ne_zero))
    · exact (differentiable_const _).mul
        (Complex.differentiable_one_div_Gamma.comp ((differentiable_id.div_const (2 : ℂ)).add_const 1))
  · simp [Complex.Gamma_one]
  · intro z
    rw [Complex.Gammaℝ_def, neg_div, Complex.cpow_neg, mul_inv, inv_inv]
    by_cases hz : z = 0
    · subst hz
      simp [Complex.Gamma_zero]
    · have key : (Complex.Gamma (z / 2))⁻¹ = z * (1 / 2 * (Complex.Gamma (z / 2 + 1))⁻¹) := by
        rw [Complex.Gamma_add_one _ (div_ne_zero hz two_ne_zero), mul_inv]
        have h2 : z * (1 / 2) * (z / 2)⁻¹ = 1 := by field_simp
        calc (Complex.Gamma (z / 2))⁻¹
            = (z * (1 / 2) * (z / 2)⁻¹) * (Complex.Gamma (z / 2))⁻¹ := by rw [h2, one_mul]
          _ = _ := by ring
      rw [key]
      ring
end PI.EF
end
end

set_option autoImplicit false
noncomputable section
open PI PI.EF
open Complex Filter Topology Set DirichletCharacter
variable {N : ℕ} [NeZero N]
namespace PI.EF
theorem _root_.solution {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (he : χ.Even)
    (h1 : χ ≠ 1) : LFunction χ 0 = 0 ∧ analyticOrderNatAt (LFunction χ) 0 = 1 := by
  obtain ⟨g, hgd, hg0, hgz⟩ := exists_differentiable_Gammaℝ_inv_eq_mul
  have hN1 : N ≠ 1 := by
    intro hN
    subst hN
    exact h1 (DirichletCharacter.level_one χ)
  have hLeq : ∀ s, LFunction χ s = completedLFunction χ s * (s * g s) := by
    intro s
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s (Or.inr hN1),
      he.gammaFactor_def, div_eq_mul_inv, hgz]
  have hc0 : completedLFunction χ 0 ≠ 0 := completed_ne_zero_left hχ (by simp) (Or.inl h1)
  have hcd : Differentiable ℂ (completedLFunction χ) :=
    DirichletCharacter.differentiable_completedLFunction h1
  refine ⟨by rw [hLeq]; simp, ?_⟩
  have hLa : AnalyticAt ℂ (LFunction χ) 0 := (DirichletCharacter.differentiable_LFunction h1).analyticAt 0
  have hord : analyticOrderAt (LFunction χ) 0 = ((1 : ℕ) : ℕ∞) := by
    rw [hLa.analyticOrderAt_eq_natCast]
    refine ⟨fun s => completedLFunction χ s * g s, (hcd.mul hgd).analyticAt 0, mul_ne_zero hc0 hg0, ?_⟩
    filter_upwards with z
    rw [hLeq]
    simp only [sub_zero, pow_one, smul_eq_mul]
    ring
  simp [analyticOrderNatAt, hord]
end PI.EF
