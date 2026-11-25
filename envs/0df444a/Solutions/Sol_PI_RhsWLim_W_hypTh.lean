-- Prove2me | solution 1 for PI.RhsWLim.W.hypTh
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:22:21.173851+00:00
-- url     : https://prove2.me/submissions/79bb6eb4-385b-4aae-bd6a-a7a1afe11232

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushH
import Theorems.Thm_PI_RhsWLim_W_continuous_hq
import Theorems.Thm_PI_RhsWLim_W_hq_periodic
import Theorems.Thm_PI_RhsWLim_W_lint_shift
import Theorems.Thm_PI_RhsWLim_W_hypMeas_eq
import Theorems.Thm_PI_RhsWLim_W_normSq_sum_eq


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
open MeasureTheory Filter Topology Matrix
open scoped ENNReal
open PI PI.RhsWLim PI.RhsWLim.W
open PI.RhsWLim
namespace PI.RhsWLim.W
theorem _root_.solution : HypTh := by
  intro k T' hT'
  let L : EuclideanSpace ℂ (Fin k) ≃L[ℝ] (Fin k → ℂ) := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin k => ℂ)
  set μ' : Measure (Fin k → ℂ) := (volume : Measure (EuclideanSpace ℂ (Fin k))).map L with hμ'def
  have hH : μ'.IsAddHaarMeasure := L.isAddHaarMeasure_map _
  have hμ' : μ' = Measure.addHaarScalarFactor μ' volume • volume := Measure.isAddLeftInvariant_eq_smul μ' volume
  have hc0 : 0 < Measure.addHaarScalarFactor μ' volume :=
    Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ' volume
  set c := Measure.addHaarScalarFactor μ' volume with hcdef
  clear_value c
  refine ⟨(1 / 2) * (c : ℝ≥0∞), ?_, ?_, fun E hE => ?_⟩
  · exact mul_ne_zero (by simp) (by exact_mod_cast hc0.ne')
  · exact ENNReal.mul_ne_top (by simp) ENNReal.coe_ne_top
  have hf : Measurable (E.indicator (1 : (Fin k → ℂ) × ℂ → ℝ≥0∞)) := measurable_one.indicator hE
  have hF : Measurable (fun p : (Fin k → ℂ) × ℝ => E.indicator (1 : (Fin k → ℂ) × ℂ → ℝ≥0∞) (hq k T' p.1 p.2)) :=
    hf.comp (continuous_hq k T').measurable
  rw [← lintegral_indicator_one hE, ← hypMeas_eq k T' hf]
  unfold hypMeas hqI
  rw [mul_assoc]
  congr 1
  have e1 : ∀ (y : EuclideanSpace ℂ (Fin k)) (θ : ℝ),
      E.indicator (1 : (Fin k → ℂ) × ℂ → ℝ≥0∞)
        ((fun i => y i), (Real.sqrt (‖y‖ ^ 2 + T') : ℂ) * Complex.exp (θ * Complex.I)) =
      E.indicator (1 : (Fin k → ℂ) × ℂ → ℝ≥0∞) (hq k T' (L y) θ) := by
    intro y θ
    rw [← normSq_sum_eq]
    rfl
  simp_rw [e1]
  have hG : Measurable (fun y : Fin k → ℂ =>
      ∫⁻ θ in Set.Ioc 0 (2 * Real.pi), E.indicator (1 : (Fin k → ℂ) × ℂ → ℝ≥0∞) (hq k T' y θ)) :=
    hF.lintegral_prod_right'
  set G : (Fin k → ℂ) → ℝ≥0∞ := fun y =>
    ∫⁻ θ in Set.Ioc 0 (2 * Real.pi), E.indicator (1 : (Fin k → ℂ) × ℂ → ℝ≥0∞) (hq k T' y θ) with hGdef
  have eM : (∫⁻ y : EuclideanSpace ℂ (Fin k), G (L y)) = ∫⁻ y, G y ∂μ' :=
    (lintegral_map hG L.continuous.measurable).symm
  rw [eM, hμ', lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]
  congr 1
  rw [hGdef]
  dsimp only
  rw [lintegral_lintegral_swap hF.aemeasurable]
  exact lint_shift _ hF.lintegral_prod_left' fun θ => by simp only [hq_periodic]
end PI.RhsWLim.W
