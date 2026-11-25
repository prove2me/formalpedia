-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.setIntegral_rotAbout
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:33:14.207391+00:00
-- url     : https://prove2.me/submissions/d243398f-5eb6-427e-ae45-102c9fa52816

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_Circle
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_MeasurableEmbeddingRotAbout
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_measurePreserving_rotAbout
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_measurableEmbedding_rotAbout
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_indicator_rotAbout

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.C
open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal
namespace ReciprocityTheory.L2DbarEstimates.C
theorem _root_.solution {n : ℕ} (c : V n) {a : ℂ} (ha : ‖a‖ = 1) (R : ℝ)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : V n → E) :
    ∫ z in ball c R, g (rotAbout c a z) = ∫ z in ball c R, g z := by
  rw [← integral_indicator measurableSet_ball, ← integral_indicator measurableSet_ball,
    integral_congr_ae (Eventually.of_forall fun z => indicator_rotAbout c ha R g z)]
  exact (measurePreserving_rotAbout c ha).integral_comp (measurableEmbedding_rotAbout c ha) _
end ReciprocityTheory.L2DbarEstimates.C
