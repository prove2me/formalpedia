-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.multA_integrable_of_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:47:00.560944+00:00
-- url     : https://prove2.me/submissions/c95ef5db-9d43-47c7-926a-03964c9aa598

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_IntegrableOnCompactOfLocL2
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_integrable


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
theorem _root_.solution {α : Type*} [MeasurableSpace α] (ν : Measure α) [IsFiniteMeasure ν]
    (F : α → ℂ) (hF : AEStronglyMeasurable F ν) (h : ∫⁻ x, ‖F x‖ₑ ^ 2 ∂ν < ⊤) :
    Integrable F ν := by
  have h2 : MemLp F 2 ν := by
    refine ⟨hF, ?_⟩
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top]
    simpa using h
  exact h2.integrable one_le_two
end ReciprocityTheory.L2DbarEstimates.F
