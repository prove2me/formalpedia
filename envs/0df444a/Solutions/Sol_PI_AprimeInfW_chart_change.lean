-- Prove2me | solution 1 for PI.AprimeInfW.chart_change
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:19:03.709983+00:00
-- url     : https://prove2.me/submissions/54e0fd7d-4130-4a9e-8c78-98009f8d74ba

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_ChartChg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.AprimeInfW
open MeasureTheory Topology
namespace PI.AprimeInfW
theorem _root_.solution {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] {Y : Type} [MeasurableSpace Y]
    (m : Measure Y) (χ : E → Y) (V : Set E) (f : E → ℝ)
    (hχ : ∀ S ⊆ V, MeasurableSet S → m (χ '' S) = ∫⁻ x in S, ENNReal.ofReal (f x) ∂μ)
    (ψ : E → E) (ψ' : E → E →L[ℝ] E) (U : Set E) (hψ : ∀ x ∈ U, HasFDerivWithinAt ψ (ψ' x) U x)
    (hinj : Set.InjOn ψ U) (hψV : ψ '' U ⊆ V) (A : Set E) (hAU : A ⊆ U) (hA : MeasurableSet A) :
    m ((χ ∘ ψ) '' A) = ∫⁻ p in A, ENNReal.ofReal (|(ψ' p).det| * f (ψ p)) ∂μ := by
  have hd : ∀ x ∈ A, HasFDerivWithinAt ψ (ψ' x) A x := fun x hx => (hψ x (hAU hx)).mono hAU
  have hinjA : Set.InjOn ψ A := hinj.mono hAU
  have hmeas : MeasurableSet (ψ '' A) := measurable_image_of_fderivWithin hA hd hinjA
  rw [Set.image_comp, hχ _ ((Set.image_mono hAU).trans hψV) hmeas,
    lintegral_image_eq_lintegral_abs_det_fderiv_mul μ hA hd hinjA]
  refine lintegral_congr fun p => ?_
  rw [ENNReal.ofReal_mul (abs_nonneg _)]
end PI.AprimeInfW
