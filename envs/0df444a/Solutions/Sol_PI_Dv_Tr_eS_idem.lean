-- Prove2me | solution 1 for PI.Dv.Tr.eS_idem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:08:57.212803+00:00
-- url     : https://prove2.me/submissions/8bcf1008-0539-46a5-a94e-6f7cf8e57e73

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_ESMulESOfNeZero
import Theorems.Thm_PI_Dv_Tr_phiS_one
import Theorems.Thm_PI_Dv_Tr_mul_eS
import Theorems.Thm_PI_Dv_Tr_tau_eS

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
theorem _root_.solution (T : GoodSet K G) (s : T.S) : eS T s * eS T s = eS T s := by
  rw [mul_eS, tau_eS, phiS_one]
end PI.Dv.Tr
