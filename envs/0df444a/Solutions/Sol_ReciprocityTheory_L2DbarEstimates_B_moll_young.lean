-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.B.moll_young
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:31:10.586386+00:00
-- url     : https://prove2.me/submissions/ec1238e6-b0a4-4533-861f-8f8aa521112c

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Mollifiers_HasCompactSupport
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Mollifiers_MollEnormSqLe
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_B_moll_young_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.B
open MeasureTheory Filter Topology Set Metric
open scoped Convolution ContDiff ENNReal Pointwise
namespace ReciprocityTheory.L2DbarEstimates.B
theorem _root_.solution (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] : YoungSt E μ := by
  intro K u s hs hu
  have h := moll_young_sq E μ K u s hs hu
  have e : ∀ z : ℝ≥0∞, z ^ (ENNReal.toReal 2) = z ^ 2 := fun z => by
    rw [ENNReal.toReal_ofNat, ← ENNReal.rpow_natCast]; norm_num
  rw [eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num),
    eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num)]
  simp_rw [e]
  exact ENNReal.rpow_le_rpow h (by norm_num)
end ReciprocityTheory.L2DbarEstimates.B
