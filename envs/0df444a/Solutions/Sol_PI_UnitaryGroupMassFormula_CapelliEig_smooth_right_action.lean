-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.CapelliEig.smooth_right_action
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:51:15.457012+00:00
-- url     : https://prove2.me/submissions/c7db0cd2-d680-40bb-92c5-fb6707bea6fb

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CapelliEigenvalues_CoreDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CapelliEigenvalues_HeckeMultiplication
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_CapelliHighestWeightConjugated
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CapelliEigenvalues_Smooth
import Theorems.Thm_PI_UnitaryGroupMassFormula_CapelliEig_Hecke_multiplication


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix PI.UpqRep
open scoped ContDiff
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.CapelliEig
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace PI.UnitaryGroupMassFormula.CapelliEig
theorem _root_.solution : SmRight := by
  intro k r ε lam Hs _ _ σ hσ v hv c hc
  have key : ∀ g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ,
      gᴴ * Hpk k r * g = Hpk k r → (g * c)ᴴ * Hpk k r * (g * c) = Hpk k r := by
    intro g hg
    have h2 : cᴴ * Hpk k r * c = Hpk k r := hc
    rw [Matrix.conjTranspose_mul]
    calc cᴴ * gᴴ * Hpk k r * (g * c) = cᴴ * (gᴴ * Hpk k r * g) * c := by
          simp only [Matrix.mul_assoc]
      _ = Hpk k r := by rw [hg, h2]
  intro g₀ hg₀
  obtain ⟨U, F, hUo, hgU, hF, hEq⟩ := hv (g₀ * c) (key g₀ hg₀)
  let L := LinearMap.toContinuousLinearMap
    (LinearMap.mulRight ℝ c : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ →ₗ[ℝ] _)
  refine ⟨(fun g => g * c) ⁻¹' U, fun g => F (g * c),
    hUo.preimage (continuous_id.matrix_mul continuous_const), hgU, ?_, ?_⟩
  · have h := hF.comp (L.contDiff.contDiffOn (s := (fun g => g * c) ⁻¹' U))
      (fun g hg => by show g * c ∈ U; exact hg)
    refine h.congr fun g _ => ?_
    show F (g * c) = F (g * c)
    rfl
  · intro g _ hgH
    have hgH' : gᴴ * Hpk k r * g = Hpk k r := hgH
    show σ g (σ c v) = F (g * c)
    rw [← hEq (g * c) (by assumption) (key g hgH')]
    show σ g (σ c v) = σ (g * c) v
    rw [Hecke_multiplication k r ε lam Hs σ hσ g hgH c hc]
    rfl
end PI.UnitaryGroupMassFormula.CapelliEig
