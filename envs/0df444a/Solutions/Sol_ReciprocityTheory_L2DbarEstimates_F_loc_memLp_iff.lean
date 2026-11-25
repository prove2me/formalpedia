-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.loc_memLp_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:17:57.262897+00:00
-- url     : https://prove2.me/submissions/7f051b0e-c35f-4be1-baea-8f97917ecbc5

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_LocalizeA

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
theorem _root_.solution {M E : Type*} [MeasurableSpace M] [NormedAddCommGroup E] (ν : Measure M)
    (f : M → E) (hf : AEStronglyMeasurable f ν) :
    MemLp f 2 ν ↔ ∫⁻ x, ‖f x‖ₑ ^ 2 ∂ν < ⊤ := by
  constructor
  · intro h
    have := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (p := 2) (by norm_num) (by norm_num)).mp h.2
    simpa [ENNReal.rpow_two] using this
  · intro h
    refine ⟨hf, ?_⟩
    refine (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (p := 2) (by norm_num) (by norm_num)).mpr ?_
    simpa [ENNReal.rpow_two] using h
end ReciprocityTheory.L2DbarEstimates.F
