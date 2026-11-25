-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.setLIntegral_rotAbout
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:33:19.142004+00:00
-- url     : https://prove2.me/submissions/8c2e1796-045c-45ab-bc9e-11be21c3f143

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
    (g : V n → ℝ≥0∞) :
    ∫⁻ z in ball c R, g (rotAbout c a z) = ∫⁻ z in ball c R, g z := by
  rw [← lintegral_indicator measurableSet_ball, ← lintegral_indicator measurableSet_ball,
    lintegral_congr fun z => indicator_rotAbout c ha R g z]
  exact (measurePreserving_rotAbout c ha).lintegral_comp_emb (measurableEmbedding_rotAbout c ha) _
end ReciprocityTheory.L2DbarEstimates.C
