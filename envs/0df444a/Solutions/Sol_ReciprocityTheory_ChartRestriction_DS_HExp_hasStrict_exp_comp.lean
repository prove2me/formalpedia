-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HExp.hasStrict_exp_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:10:25.516962+00:00
-- url     : https://prove2.me/submissions/3f8eb114-720e-4c69-b112-32e570acbf1b

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
theorem _root_.solution (L : 𝔸 × 𝔸 →L[ℝ] 𝔸) :
    HasStrictFDerivAt (fun p : 𝔸 × 𝔸 => exp (L p)) L (0 : 𝔸 × 𝔸) := by
  have h1 : HasStrictFDerivAt (exp : 𝔸 → 𝔸) (ContinuousLinearMap.id ℝ 𝔸) (L 0) := by
    rw [map_zero]; exact hasStrictFDerivAt_exp_zero_alt
  exact h1.comp (0 : 𝔸 × 𝔸) L.hasStrictFDerivAt
end ReciprocityTheory.ChartRestriction.DS.HExp
