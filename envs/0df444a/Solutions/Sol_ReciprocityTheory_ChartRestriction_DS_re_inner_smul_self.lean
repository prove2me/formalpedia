-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.re_inner_smul_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:14:03.188804+00:00
-- url     : https://prove2.me/submissions/ccd702fb-959a-4d77-92d7-b3b1610a8f54

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_WeightBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasimirGapAtNoncompactWeight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_NcBound

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
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (c : ℝ) (x : M) :
    RCLike.re (inner ℂ ((c : ℂ) • x) x) = c * ‖x‖ ^ 2 := by
  rw [inner_smul_left, inner_self_eq_norm_sq_to_K]
  simp [← Complex.ofReal_pow]
end ReciprocityTheory.ChartRestriction.DS
