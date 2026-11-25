-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartChange_lintegral_split_22e51e01810a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:36:39.065191+00:00
-- url     : https://prove2.me/submissions/cac5d85f-e812-4fce-9b1d-9b7fc4f531f6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarIntChartChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartChangeSheetNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartChangeLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLinearNoetherNormalization
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPosPartSplit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PIntegralIndependent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PVarIntChartChange
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IntegralIndep_measurable_chartPosDens_47c1c9528926


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
open MvPolynomial MeasureTheory Matrix ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.ChartChange
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.ChartChange
theorem _root_.solution {K : Ideal (MvPolynomial (Fin n) ℂ)} {B : Matrix (Fin d) (Fin n) ℂ}
    {w : (Fin n → ℂ) → ℝ} (ψ : Fin d → (Fin n → ℂ) → ℝ) {F : ℕ → Set (Fin n → ℂ)}
    (hB : IsFiniteProjection K B) (hw : Measurable w) (hFm : ∀ k, MeasurableSet (F k))
    (h : ∀ᵐ y, ENNReal.ofReal (chartPosDens K B w ψ y) =
      ∑' k, ENNReal.ofReal (chartPosDens K B ((F k).indicator w) ψ y)) :
    ∫⁻ y, ENNReal.ofReal (chartPosDens K B w ψ y) =
      ∑' k, ∫⁻ y, ENNReal.ofReal (chartPosDens K B ((F k).indicator w) ψ y) := by
  rw [lintegral_congr_ae h, lintegral_tsum fun k =>
    (IntegralIndep.measurable_chartPosDens hB (hw.indicator (hFm k)) ψ).ennreal_ofReal.aemeasurable]
end GroundTheory.Heights₂.Heights.ChartChange
