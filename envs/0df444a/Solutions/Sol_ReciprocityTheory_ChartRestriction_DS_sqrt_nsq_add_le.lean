-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.sqrt_nsq_add_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:19:22.881933+00:00
-- url     : https://prove2.me/submissions/49f9bc18-8b67-4665-90cd-895cf22e268d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_LayerSpan
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Numerics
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_KUnitB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_WeightBound
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_sqrt_nsq_eq_norm__fa929b459380

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
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (x y : Fin n → ℝ) : √(nsq (x + y)) ≤ √(nsq x) + √(nsq y) := by
  rw [sqrt_nsq_eq_norm', sqrt_nsq_eq_norm', sqrt_nsq_eq_norm']
  first
    | (rw [WithLp.toLp_add]; exact norm_add_le _ _)
    | (have h := norm_add_le (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)) (WithLp.toLp 2 y)
       rwa [← WithLp.toLp_add] at h)
end ReciprocityTheory.ChartRestriction.DS
