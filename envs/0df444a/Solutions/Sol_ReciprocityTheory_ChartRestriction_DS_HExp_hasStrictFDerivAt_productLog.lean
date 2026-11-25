-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HExp.hasStrictFDerivAt_productLog
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:24:56.967031+00:00
-- url     : https://prove2.me/submissions/39f3539f-fcba-4b5f-9048-ffadbf6cb45e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_HaarVolumes_HaarExpA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_HaarVolumes_HaarExpB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HExp_hasStrict_mul

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
theorem _root_.solution : HasStrictFDerivAt (F2 (𝔸 := 𝔸))
    (ContinuousLinearMap.fst ℝ 𝔸 𝔸 + ContinuousLinearMap.snd ℝ 𝔸 𝔸) 0 :=
  hasStrict_mul (ContinuousLinearMap.fst ℝ 𝔸 𝔸) (ContinuousLinearMap.snd ℝ 𝔸 𝔸)
end ReciprocityTheory.ChartRestriction.DS.HExp
