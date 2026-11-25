-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.BetaLUniq.EigA.eq_zero_of_norm_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:37:49.646919+00:00
-- url     : https://prove2.me/submissions/b4f0e66f-5f22-4a76-8fa7-d71717f859cf

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BetaUniqueness_EqZeroOfNormLtOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.BetaLUniq PI.UnitaryGroupMassFormula.BetaLUniq.EigA
variable {E : Type} [Field E] [NumberField E]
namespace PI.UnitaryGroupMassFormula.BetaLUniq.EigA
theorem _root_.solution (x : 𝓞 E) (h : ∀ φ : E →+* ℂ, ‖φ (algebraMap (𝓞 E) E x)‖ < 1) :
    x = 0 := by
  classical
  by_contra hx
  set y : E := algebraMap (𝓞 E) E x with hy
  have hne : Algebra.norm ℤ x ≠ 0 := by
    rwa [Ne, Algebra.norm_eq_zero_iff]
  have hQ : ((Algebra.norm ℤ x : ℤ) : ℚ) = Algebra.norm ℚ y := Algebra.coe_norm_int x
  have hC := Algebra.norm_eq_prod_embeddings ℚ ℂ y
  rw [← hQ, map_intCast] at hC
  let σ0 : E →ₐ[ℚ] ℂ := IsAlgClosed.lift
  have hlt : ‖∏ σ : E →ₐ[ℚ] ℂ, σ y‖ < 1 := by
    rw [norm_prod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ σ0)]
    have h0 : ‖σ0 y‖ < 1 := h σ0.toRingHom
    have h1 : ∏ σ ∈ Finset.univ.erase σ0, ‖σ y‖ ≤ 1 :=
      Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun σ _ => (h σ.toRingHom).le)
    calc ‖σ0 y‖ * ∏ σ ∈ Finset.univ.erase σ0, ‖σ y‖ ≤ ‖σ0 y‖ * 1 :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ < 1 := by rwa [mul_one]
  rw [← hC] at hlt
  have h1 : (1 : ℝ) ≤ ‖((Algebra.norm ℤ x : ℤ) : ℂ)‖ := by
    rw [Complex.norm_intCast]
    exact_mod_cast Int.one_le_abs hne
  linarith
end PI.UnitaryGroupMassFormula.BetaLUniq.EigA
