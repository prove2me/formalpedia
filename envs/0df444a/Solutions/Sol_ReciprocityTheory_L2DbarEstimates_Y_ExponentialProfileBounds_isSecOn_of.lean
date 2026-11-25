-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.ExponentialProfileBounds.isSecOn_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:30:47.473831+00:00
-- url     : https://prove2.me/submissions/592e9c38-fdd8-4ea1-9767-dd035079a138

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LogNormSq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_EuclideanAtlasPointwiseNormSqUnitSection

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal Matrix
noncomputable section
open ReciprocityTheory.L2DbarEstimates.Y.ExponentialProfileBounds
variable {n : ℕ}
namespace ReciprocityTheory.L2DbarEstimates.Y.ExponentialProfileBounds
theorem _root_.solution (la : ℤ) (U : Set (V n)) (f : Unit → V n → ℂ) (hf : Differentiable ℂ (f ())) :
    (atlas n).IsSecOn la U f := ⟨fun i => (hf.comp differentiable_id).differentiableOn, fun i j y _ _ _ => by cases i; cases j; simp [atlas]⟩
end ReciprocityTheory.L2DbarEstimates.Y.ExponentialProfileBounds
