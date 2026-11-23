-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HExp.logA_exp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:03:19.279806+00:00
-- url     : https://prove2.me/submissions/bdd8101c-c6f2-476e-8bb3-87e6bd07789f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_HaarVolumes_HaarExpA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_HaarVolumes_HaarExpB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HExp
open Filter Topology Metric NormedSpace Asymptotics
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
namespace ReciprocityTheory.ChartRestriction.DS.HExp
theorem _root_.solution : ∀ᶠ X in 𝓝 (0 : 𝔸), logA 𝔸 (exp X) = X :=
  (hasStrictFDerivAt_exp_zero_alt (𝔸 := 𝔸)).eventually_left_inverse
end ReciprocityTheory.ChartRestriction.DS.HExp
