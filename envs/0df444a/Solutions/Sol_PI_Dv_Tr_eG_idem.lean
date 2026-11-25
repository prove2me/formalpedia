-- Prove2me | solution 1 for PI.Dv.Tr.eG_idem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:29:55.590805+00:00
-- url     : https://prove2.me/submissions/26325ef0-f69d-4bec-983c-24bf47939514

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_ESMulESOfNeZero
import Theorems.Thm_PI_Dv_Tr_eS_idem
import Theorems.Thm_PI_Dv_Tr_eS_orth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.Tr
open PI.Dv
variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G]
namespace PI.Dv.Tr
theorem _root_.solution (T : GoodSet K G) : eG T * eG T = eG T := by
  classical
  rw [eG, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.sum_eq_single t]
  · exact eS_idem T t
  · intro s _ hs; exact eS_orth T s t hs
  · simp
end PI.Dv.Tr
