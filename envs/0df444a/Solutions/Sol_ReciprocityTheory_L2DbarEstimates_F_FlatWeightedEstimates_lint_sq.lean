-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.FlatWeightedEstimates.lint_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:13:38.163893+00:00
-- url     : https://prove2.me/submissions/35e1f784-1612-4098-9bee-985d75fe2a84

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Mollifiers_MollifierL2LocTendsto
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_IntegrableFd

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
open ReciprocityTheory.L2DbarEstimates.F.FlatWeightedEstimates
namespace ReciprocityTheory.L2DbarEstimates.F.FlatWeightedEstimates
theorem _root_.solution {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] (f : α → E)
    (μ : Measure α) : ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ = eLpNorm f 2 μ ^ 2 := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (f := f) (μ := μ) (p := 2) two_ne_zero
  have e : ((2 : NNReal) : ℝ) = ((2 : ℕ) : ℝ) := by norm_num
  rw [e] at h
  simp only [ENNReal.rpow_natCast] at h
  simpa using h.symm
end ReciprocityTheory.L2DbarEstimates.F.FlatWeightedEstimates
