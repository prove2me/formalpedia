-- Prove2me | solution 2 for ReciprocityTheory.ChartRestriction.DS.nsq_root
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:17:16.76491+00:00
-- url     : https://prove2.me/submissions/b027fb4c-4525-4f8a-8761-8327631fbd3b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasValK
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_NumRho
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_numRho_dot_root_left

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
theorem _root_.solution {a b : Fin n} (hab : a ≠ b) : nsq (root a b) = 2 := by
  rw [nsq, numRho_dot_root_left]
  simp [root, Pi.single_apply, hab, Ne.symm hab] <;> norm_num
end ReciprocityTheory.ChartRestriction.DS
