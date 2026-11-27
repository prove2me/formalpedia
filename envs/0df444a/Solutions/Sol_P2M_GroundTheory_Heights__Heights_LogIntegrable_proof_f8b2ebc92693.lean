-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LogIntegrable_proof_f8b2ebc92693
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:03:36.293863+00:00
-- url     : https://prove2.me/submissions/d735b384-96f6-45cb-b4f9-a412da3d1c05

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsSheetMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarSlabMeasure
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLogIntegrable
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogIntegrableProof_lintegral_lt_top_9a2bece62d68

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Set Filter ComplexSets
open scoped ENNReal
noncomputable section
open LogIntegrableProof
namespace GroundTheory.Heights₂.Heights
namespace LogIntegrable
theorem _root_.solution (hM : SheetSumMeasurable.Statement) (hD : ChartMassCompare.Statement)
    (hS : VarSlabMeasure.Statement) (hF : MassFinite.Statement) : LogIntegrable.Statement := by
  intro n d J A u φ R hJ hdim hA hu hφ
  have hcont : Continuous fun x : Fin n → ℂ => linEval u x := by unfold linEval; fun_prop
  have hwm : Measurable fun x : Fin n → ℂ => Real.log ‖linEval u x‖ :=
    Real.measurable_log.comp (continuous_norm.comp hcont).measurable
  refine ⟨(hM n d J A _ φ hJ hdim hA (hwm.indicator measurableSet_closedBall) hφ).2.aestronglyMeasurable,
    ?_⟩
  obtain ⟨K, hK, hDK⟩ := hD n d J A φ R hJ hdim hA hφ

  obtain ⟨L, hL0, hL⟩ : ∃ L : ℝ, 0 ≤ L ∧
      ∀ z : EuclideanSpace ℂ (Fin n), ‖z‖ ≤ L * ‖WithLp.ofLp z‖ :=
    ⟨(n : ℝ) ^ (2⁻¹ : ℝ), by positivity, fun z => by
      simpa [dist_zero_right] using
        (PiLp.lipschitzWith_toLp 2 (fun _ : Fin n => ℂ)).dist_le_mul (WithLp.ofLp z) 0⟩
  unfold HasFiniteIntegral
  refine (hDK _ hwm).trans_lt (ENNReal.mul_lt_top hK ?_)
  refine lt_of_le_of_lt (lintegral_mono_set ?_) (lintegral_lt_top hS hF u (L * R) hJ hdim hu)
  rintro z ⟨hz, hzB⟩
  refine ⟨hz, ?_⟩
  have : ‖WithLp.ofLp z‖ ≤ R := mem_closedBall_zero_iff.mp hzB
  exact (hL z).trans (mul_le_mul_of_nonneg_left this hL0)
end LogIntegrable
end GroundTheory.Heights₂.Heights
