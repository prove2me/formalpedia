-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HExp.exp_mul_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:11:41.498801+00:00
-- url     : https://prove2.me/submissions/8918f29e-3166-46e2-87fa-851381e1e1aa

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_HaarVolumes_HaarExpA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_HaarVolumes_HaarExpB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HExp_exp_neg_mul

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
theorem _root_.solution (X : 𝔸) : exp X * exp (-X) = 1 := by
  have := exp_neg_mul (-X)
  rwa [neg_neg] at this
end ReciprocityTheory.ChartRestriction.DS.HExp
