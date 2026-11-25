-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.dbarDir_continuous_hasCompactSupport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:04:54.469499+00:00
-- url     : https://prove2.me/submissions/aefaf9be-53d8-435f-bd48-cbc003953501

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtCut
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloWeak
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_MollifyEqConvolution
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtWeakA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtWeak

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
open scoped ENNReal ContDiff
variable {n : ℕ}
namespace ReciprocityTheory.L2DbarEstimates.C
theorem _root_.solution {g : V n → ℂ} (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) (v : V n) :
    Continuous (fun z => dbarDir g z v) ∧ HasCompactSupport (fun z => dbarDir g z v) := by
  have hd : Continuous (fderiv ℝ g) := hg.continuous_fderiv (by simp)
  refine ⟨?_, ?_⟩
  · unfold dbarDir
    exact (hd.clm_apply continuous_const).sub
      (continuous_const.mul (hd.clm_apply continuous_const))
  · unfold dbarDir
    exact (hc.fderiv_apply ℝ (I • v)).sub ((hc.fderiv_apply ℝ v).mul_left)
end ReciprocityTheory.L2DbarEstimates.C
