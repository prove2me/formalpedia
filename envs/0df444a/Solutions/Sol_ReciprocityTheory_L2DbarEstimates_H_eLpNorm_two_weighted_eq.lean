-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.H.eLpNorm_two_weighted_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:41:55.280822+00:00
-- url     : https://prove2.me/submissions/1647b110-31d7-4c3e-8f0f-76ab88c0f4fe

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_SkodaWeightStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_WeightedIntegralEqLintegral
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_weightedIntegral_eq_lintegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.H
open MeasureTheory ReciprocityTheory.L2DbarEstimates
open scoped ENNReal InnerProductSpace
namespace ReciprocityTheory.L2DbarEstimates.H
theorem _root_.solution (n : ℕ) {M : Type*} [MeasurableSpace M] (z : M → V n) {ψ : M → ℝ}
    (hψ : Measurable ψ) (f : M → ℂ) :
    eLpNorm f 2 (wvol n z ψ) = wint n z f ψ ^ (1 / (2 : ℝ)) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num), ENNReal.toReal_ofNat,
    ← weightedIntegral_eq_lintegral n z hψ f]
end ReciprocityTheory.L2DbarEstimates.H
