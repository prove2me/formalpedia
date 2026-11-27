-- Prove2me | solution 1 for P2M_PI_EF_order_Gamma__inv_zero_3dfd6220d618
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:14:54.012814+00:00
-- url     : https://prove2.me/submissions/10a431c4-6fcf-4169-a33e-242c8b58693a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LStructB
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
theorem _root_.solution : analyticOrderAt (fun s : ℂ => (Gammaℝ s)⁻¹) 0 = 1 := by
  obtain ⟨g, hgd, hg0, hgz⟩ := exists_differentiable_Gammaℝ_inv_eq_mul
  show analyticOrderAt _ _ = ((1 : ℕ) : ℕ∞)
  rw [(Complex.differentiable_Gammaℝ_inv.analyticAt 0).analyticOrderAt_eq_natCast]
  refine ⟨g, hgd.analyticAt 0, hg0, ?_⟩
  filter_upwards with z
  rw [hgz z]
  simp
end PI.EF
