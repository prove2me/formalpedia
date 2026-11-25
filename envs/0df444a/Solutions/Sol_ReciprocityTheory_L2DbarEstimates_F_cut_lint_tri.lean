-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.cut_lint_tri
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:08:41.769876+00:00
-- url     : https://prove2.me/submissions/c19ec44a-c1d7-4d74-a046-264d71ca24d4

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_CutoffA

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
theorem _root_.solution {M : Type*} [MeasurableSpace M] (μ : Measure M) (F G H : M → ℝ≥0∞)
    (hG : AEMeasurable G μ) (h : ∀ x, F x ≤ 2 * H x + 2 * G x) :
    ∫⁻ x, F x ∂μ ≤ 2 * ∫⁻ x, H x ∂μ + 2 * ∫⁻ x, G x ∂μ := by
  calc ∫⁻ x, F x ∂μ ≤ ∫⁻ x, (2 * H x + 2 * G x) ∂μ := lintegral_mono h
    _ = ∫⁻ x, 2 * H x ∂μ + ∫⁻ x, 2 * G x ∂μ := lintegral_add_right' _ (hG.const_mul 2)
    _ = 2 * ∫⁻ x, H x ∂μ + 2 * ∫⁻ x, G x ∂μ := by
        rw [lintegral_const_mul' _ _ (by simp), lintegral_const_mul' _ _ (by simp)]
end ReciprocityTheory.L2DbarEstimates.F
