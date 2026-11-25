-- Prove2me | solution 1 for PI.Residue.prod_position
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:19:08.478162+00:00
-- url     : https://prove2.me/submissions/e91f68b0-c83f-498b-a9fa-5206e569783b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_FactorizationMultisetProd
import Theorems.Thm_PI_Residue_position_cons

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
theorem _root_.solution [Fintype ι] (N : α → ℕ) (idx : α → ι) (s : Multiset α) :
    ∏ i, intersection_update_fsHerm_neg_one N idx s i = (s.map N).prod := by
  induction s using Multiset.induction_on with
  | empty => simp [intersection_update_fsHerm_neg_one]
  | cons a s ih =>
    simp_rw [position_cons]
    rw [Finset.prod_mul_distrib, ih]
    simp
end PI.Residue
