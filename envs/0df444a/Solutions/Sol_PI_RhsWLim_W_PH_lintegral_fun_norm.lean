-- Prove2me | solution 1 for PI.RhsWLim.W.PH.lintegral_fun_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:13:33.118339+00:00
-- url     : https://prove2.me/submissions/8b610041-fb33-46be-99aa-73de79a6318e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_PolarHyp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal
open PI PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.PH
namespace PI.RhsWLim.W.PH
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [Nontrivial E] (μ : Measure E) [μ.IsAddHaarMeasure]
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ x, F ‖x‖ ∂μ = μ.toSphere univ *
      ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (y ^ (Module.finrank ℝ E - 1)) * F y := by
  calc ∫⁻ x, F ‖x‖ ∂μ = ∫⁻ x : ({(0 : E)}ᶜ : Set E), F ‖x.1‖ ∂(μ.comap (↑)) := by
        rw [lintegral_subtype_comap (measurableSet_singleton _).compl (fun x => F ‖x‖),
          restrict_compl_singleton]
    _ = ∫⁻ p, F (p.2 : ℝ) ∂(μ.toSphere.prod (Measure.volumeIoiPow (Module.finrank ℝ E - 1))) := by
        rw [← (μ.measurePreserving_homeomorphUnitSphereProd).lintegral_comp_emb
          (Homeomorph.measurableEmbedding _)]
        simp
    _ = μ.toSphere univ * ∫⁻ y : Ioi (0 : ℝ), F y ∂(Measure.volumeIoiPow (Module.finrank ℝ E - 1)) := by
        rw [lintegral_prod (fun p : (Metric.sphere (0 : E) 1) × Ioi (0 : ℝ) => F (p.2 : ℝ))
          (hF.comp (measurable_subtype_coe.comp measurable_snd)).aemeasurable]
        dsimp only
        rw [lintegral_const, mul_comm]
    _ = _ := by
        have hw := lintegral_withDensity_eq_lintegral_mul (Measure.comap Subtype.val volume)
          (f := fun r : Ioi (0 : ℝ) => ENNReal.ofReal ((r : ℝ) ^ (Module.finrank ℝ E - 1))) (by fun_prop)
          (g := fun y : Ioi (0 : ℝ) => F y) (hF.comp measurable_subtype_coe)
        rw [Measure.volumeIoiPow, hw]
        simp only [Pi.mul_apply, Function.comp_apply]
        rw [lintegral_subtype_comap measurableSet_Ioi (fun y : ℝ => ENNReal.ofReal (y ^ (Module.finrank ℝ E - 1)) * F y)]
end PI.RhsWLim.W.PH
