-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_DS_nsq_nonneg__b8329bf5ba4b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:51:24.189699+00:00
-- url     : https://prove2.me/submissions/1b6ff29d-8cde-473e-8939-56ad83a28af3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_LayerSpan
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Numerics
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_KUnitB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_WeightBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (x : Fin n → ℝ) : 0 ≤ nsq x := by
  unfold nsq dot
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)
end ReciprocityTheory.ChartRestriction.DS
