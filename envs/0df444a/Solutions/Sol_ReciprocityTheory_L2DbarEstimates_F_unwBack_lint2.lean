-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.unwBack_lint2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:16:03.008838+00:00
-- url     : https://prove2.me/submissions/ed81ec6d-f6c3-4e72-a8a9-cd365ace6113

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_unwBack_lint
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_ofReal


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.F
theorem _root_.solution {M : Type*} [MeasurableSpace M] (μ : Measure M) (F A B : M → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (hA : ∀ x, 0 ≤ A x) (hB : ∀ x, 0 ≤ B x)
    (hBm : AEMeasurable (fun x => ENNReal.ofReal (B x)) μ) (h : ∀ x, F x ≤ C * (A x + B x)) :
    ∫⁻ x, ENNReal.ofReal (F x) ∂μ ≤ ENNReal.ofReal C *
      (∫⁻ x, ENNReal.ofReal (A x) ∂μ + ∫⁻ x, ENNReal.ofReal (B x) ∂μ) := by
  calc ∫⁻ x, ENNReal.ofReal (F x) ∂μ
      ≤ ENNReal.ofReal C * ∫⁻ x, ENNReal.ofReal (A x + B x) ∂μ :=
        unwBack_lint μ F (fun x => A x + B x) C hC h
    _ = ENNReal.ofReal C * (∫⁻ x, ENNReal.ofReal (A x) ∂μ + ∫⁻ x, ENNReal.ofReal (B x) ∂μ) := by
        rw [← lintegral_add_right' (fun x => ENNReal.ofReal (A x)) hBm]
        congr 1
        exact lintegral_congr fun x => ENNReal.ofReal_add (hA x) (hB x)
end ReciprocityTheory.L2DbarEstimates.F
