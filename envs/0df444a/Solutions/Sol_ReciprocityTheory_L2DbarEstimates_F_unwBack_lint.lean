-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.unwBack_lint
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:35:12.023549+00:00
-- url     : https://prove2.me/submissions/dcd7e77b-f3df-44e5-9214-62f2f33d8e83

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackA
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
theorem _root_.solution {M : Type*} [MeasurableSpace M] (μ : Measure M) (F G : M → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (h : ∀ x, F x ≤ C * G x) :
    ∫⁻ x, ENNReal.ofReal (F x) ∂μ ≤ ENNReal.ofReal C * ∫⁻ x, ENNReal.ofReal (G x) ∂μ := by
  calc ∫⁻ x, ENNReal.ofReal (F x) ∂μ ≤ ∫⁻ x, ENNReal.ofReal C * ENNReal.ofReal (G x) ∂μ :=
        lintegral_mono fun x => by
          rw [← ENNReal.ofReal_mul hC]
          exact ENNReal.ofReal_le_ofReal (h x)
    _ = ENNReal.ofReal C * ∫⁻ x, ENNReal.ofReal (G x) ∂μ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
end ReciprocityTheory.L2DbarEstimates.F
