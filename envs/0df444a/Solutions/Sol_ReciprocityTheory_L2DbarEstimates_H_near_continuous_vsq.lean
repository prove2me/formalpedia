-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.H.near_continuous_vsq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:15:41.620047+00:00
-- url     : https://prove2.me/submissions/ef5fe65e-2dc3-4a62-bfc6-72ae031e151c

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_SmoothRLog
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_WeightedIntegralEqLintegral
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_NearContinuousOfSmoothR

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
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.H
theorem _root_.solution {M : Type*} [TopologicalSpace M] {p : ℕ} (g : Fin p → M → ℂ)
    (hg : ∀ l, Continuous (g l)) : Continuous (fun x => vsq (gv g x)) := by
  unfold vsq gv
  exact continuous_finset_sum _ fun i _ => ((hg i).norm).pow 2
end ReciprocityTheory.L2DbarEstimates.H
