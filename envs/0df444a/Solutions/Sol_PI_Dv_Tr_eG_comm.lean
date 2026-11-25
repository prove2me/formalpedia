-- Prove2me | solution 1 for PI.Dv.Tr.eG_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:56:37.925577+00:00
-- url     : https://prove2.me/submissions/39d45744-9cdc-4670-838b-6d953d2ebbd4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_ESMulESOfNeZero
import Theorems.Thm_PI_Dv_Tr_eS_comm

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
theorem _root_.solution (T : GoodSet K G) (a : MonoidAlgebra K G) : a * eG T = eG T * a := by
  rw [eG, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun s _ => eS_comm T s a
end PI.Dv.Tr
