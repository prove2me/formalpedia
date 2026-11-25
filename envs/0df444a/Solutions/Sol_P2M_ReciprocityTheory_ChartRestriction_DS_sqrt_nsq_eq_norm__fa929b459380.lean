-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_DS_sqrt_nsq_eq_norm__fa929b459380
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:51:35.922728+00:00
-- url     : https://prove2.me/submissions/8c79bbb3-7d62-410d-9b0a-8a788b27a98a

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
theorem _root_.solution (x : Fin n → ℝ) :
    √(nsq x) = ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))‖ := by
  first
    | (rw [EuclideanSpace.norm_eq]
       congr 1
       simp [nsq, dot, Real.norm_eq_abs, sq])
    | (rw [EuclideanSpace.norm_eq]
       congr 1
       simp only [nsq, dot, PiLp.toLp_apply, Real.norm_eq_abs, sq_abs, sq])
end ReciprocityTheory.ChartRestriction.DS
