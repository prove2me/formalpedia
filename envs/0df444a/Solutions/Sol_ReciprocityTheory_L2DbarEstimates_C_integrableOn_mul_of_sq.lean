-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.integrableOn_mul_of_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:02:29.689513+00:00
-- url     : https://prove2.me/submissions/a099600b-b8ed-4a30-addb-cac844582e22

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
theorem _root_.solution {W : Set (V n)} {u h : V n → ℂ}
    (hum : AEStronglyMeasurable u (volume.restrict W)) (hu2 : IntegrableOn (fun z => ‖u z‖ ^ 2) W)
    (hc : Continuous h) (hs : HasCompactSupport h) : IntegrableOn (fun z => u z * h z) W := by
  have hh2 : Integrable (fun z => ‖h z‖ ^ 2) :=
    (hc.norm.pow 2).integrable_of_hasCompactSupport
      (hs.mono (fun z hz => by
        rw [Function.mem_support] at hz ⊢
        intro h0
        exact hz (by simp [h0])))
  refine Integrable.mono' ((hu2.add hh2.integrableOn).div_const 2)
    (hum.mul hc.aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall (fun z => ?_)
  simp only [Pi.add_apply, norm_mul]
  nlinarith [sq_nonneg (‖u z‖ - ‖h z‖), norm_nonneg (u z), norm_nonneg (h z)]
end ReciprocityTheory.L2DbarEstimates.C
