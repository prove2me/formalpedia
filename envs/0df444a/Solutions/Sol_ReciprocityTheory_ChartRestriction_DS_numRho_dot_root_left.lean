-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.numRho_dot_root_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:14:02.501298+00:00
-- url     : https://prove2.me/submissions/5d3db8db-a5a1-455e-a6f4-cdb34ed22dea

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasValK
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_NumRho

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
variable {ε : Fin n → Bool}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (a b : Fin n) (v : Fin n → ℝ) : dot (root a b) v = v a - v b := by
  simp [dot, root, sub_mul, Finset.sum_sub_distrib, Pi.single_apply]
end ReciprocityTheory.ChartRestriction.DS
