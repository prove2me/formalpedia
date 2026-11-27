-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.DjC.mul_hom_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:16:41.786257+00:00
-- url     : https://prove2.me/submissions/95c84726-2883-4a4d-bda5-b62de109901a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CoreStar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SumEqSumCompEmbedding
import Definitions.Def_Lemmata_B110_ExistsMoved
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_DjCurveA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.UnitaryCorollaryDerivatives PI.UnitaryCorollaryDerivatives.DjC
namespace PI.UnitaryCorollaryDerivatives.DjC
theorem _root_.solution (φ : ℝ → ℂ) (c : ℂ) (hmul : ∀ s t, φ (s + t) = φ s * φ t) (h1 : φ 0 = 1)
    (h0 : HasDerivAt φ c 0) (t : ℝ) : φ t = Complex.exp (t * c) := by
  have hd : ∀ t, HasDerivAt φ (φ t * c) t := by
    intro t
    have h1' : HasDerivAt (fun s => φ (s - t)) c t := by
      have h00 := h0
      rw [← sub_self t] at h00
      exact h00.comp_sub_const t t
    have h2 := h1'.const_mul (φ t)
    refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    show φ s = φ t * φ (s - t)
    rw [← hmul]; congr 1; ring
  let ψ : ℝ → ℂ := fun t => φ t * Complex.exp (-((t : ℂ) * c))
  have hψ : ∀ t, HasDerivAt ψ 0 t := by
    intro t
    have e0 : HasDerivAt (fun t : ℝ => -((t : ℂ) * c)) (-(1 * c)) t := by
      have h := ((hasDerivAt_id t).ofReal_comp.mul_const c).fun_neg
      simpa using h
    have e1 := e0.cexp
    have h3 := (hd t).fun_mul e1
    have h4 : φ t * c * Complex.exp (-((t : ℂ) * c)) +
        φ t * (Complex.exp (-((t : ℂ) * c)) * -(1 * c)) = 0 := by ring
    rw [h4] at h3
    exact h3
  have hc := is_const_of_deriv_eq_zero (fun t => (hψ t).differentiableAt) (fun t => (hψ t).deriv) t 0
  simp only [ψ, h1, Complex.ofReal_zero, zero_mul, neg_zero, Complex.exp_zero, mul_one] at hc
  rw [Complex.exp_neg] at hc
  exact eq_of_mul_inv_eq_one hc
end PI.UnitaryCorollaryDerivatives.DjC
