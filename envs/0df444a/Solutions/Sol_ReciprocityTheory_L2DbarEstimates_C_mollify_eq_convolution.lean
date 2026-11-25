-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.mollify_eq_convolution
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:08:43.951416+00:00
-- url     : https://prove2.me/submissions/d1dd1e21-1d9c-4e29-992f-e5f52e485c0c

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloContDiffStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_IntegralMollProfBall
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_MollifyEqConvolution

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
open scoped ENNReal ContDiff Convolution
namespace ReciprocityTheory.L2DbarEstimates.C
theorem _root_.solution (n : ℕ) (t : ℝ) (u : V n → ℂ) :
    mollify n t u = (moll n t) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u := by
  funext x
  rw [convolution_eq_swap]
  simp only [mollify, ContinuousLinearMap.lsmul_apply, Complex.real_smul]
end ReciprocityTheory.L2DbarEstimates.C
