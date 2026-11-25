-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HExp.hasStrictFDerivAt_translateLog
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:25:01.133982+00:00
-- url     : https://prove2.me/submissions/c9c0b679-2ea4-4941-896e-dd13da725982

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
theorem _root_.solution : HasStrictFDerivAt (F1 (𝔸 := 𝔸)) (ContinuousLinearMap.snd ℝ 𝔸 𝔸) 0 := by
  have := hasStrict_mul (-(ContinuousLinearMap.fst ℝ 𝔸 𝔸))
    (ContinuousLinearMap.fst ℝ 𝔸 𝔸 + ContinuousLinearMap.snd ℝ 𝔸 𝔸)
  refine this.congr_fderiv ?_
  ext p <;> simp
end ReciprocityTheory.ChartRestriction.DS.HExp
