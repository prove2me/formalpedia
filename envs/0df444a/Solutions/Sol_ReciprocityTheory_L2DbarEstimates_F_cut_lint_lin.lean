-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.cut_lint_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:08:38.726985+00:00
-- url     : https://prove2.me/submissions/fda99aec-7eb9-41f6-b6f9-c847fdf6e55a

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_CutoffA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_Cutoff
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
theorem _root_.solution {M : Type*} [MeasurableSpace M] (μ : Measure M) (G H : M → ℝ≥0∞)
    (hG : AEMeasurable G μ) (p q : ℝ) (hGf : ∫⁻ x, G x ∂μ < ⊤) (hHf : ∫⁻ x, H x ∂μ < ⊤) :
    ∫⁻ x, (ENNReal.ofReal p * G x + ENNReal.ofReal q * H x) ∂μ < ⊤ := by
  rw [lintegral_add_left' (hG.const_mul _), lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hGf,
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top hHf⟩
end ReciprocityTheory.L2DbarEstimates.F
