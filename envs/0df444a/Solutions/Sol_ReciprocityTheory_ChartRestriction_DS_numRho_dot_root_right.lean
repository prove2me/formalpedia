-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.numRho_dot_root_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:23:31.070383+00:00
-- url     : https://prove2.me/submissions/033916da-9eb6-4915-beea-71f9801cfcfd

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
theorem _root_.solution (a b : Fin n) (v : Fin n → ℝ) : dot v (root a b) = v a - v b := by
  simp [dot, root, mul_sub, Finset.sum_sub_distrib, Pi.single_apply]
end ReciprocityTheory.ChartRestriction.DS
