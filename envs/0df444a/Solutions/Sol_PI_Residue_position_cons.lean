-- Prove2me | solution 1 for PI.Residue.position_cons
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:12:51.912223+00:00
-- url     : https://prove2.me/submissions/10ef4a06-64ae-4095-aaa2-be056da2cd0d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_FactorizationMultisetProd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.Residue
open scoped ENNReal
variable {α ι : Type*} [DecidableEq α] [DecidableEq ι]
namespace PI.Residue
theorem _root_.solution (N : α → ℕ) (idx : α → ι) (a : α) (s : Multiset α) (i : ι) :
    intersection_update_fsHerm_neg_one N idx (a ::ₘ s) i = (if idx a = i then N a else 1) * intersection_update_fsHerm_neg_one N idx s i := by
  unfold intersection_update_fsHerm_neg_one
  by_cases h : idx a = i
  · simp [h]
  · simp [h]
end PI.Residue
