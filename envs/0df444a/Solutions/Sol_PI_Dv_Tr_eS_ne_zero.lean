-- Prove2me | solution 1 for PI.Dv.Tr.eS_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:14:34.786533+00:00
-- url     : https://prove2.me/submissions/ef45226e-9c5a-4577-afa2-f188a11afd79

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_ESMulESOfNeZero
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
theorem _root_.solution (T : GoodSet K G) (s : T.S) : eS T s ≠ 0 := by
  intro h
  have := tau_eS T s
  rw [h, map_zero] at this
  exact zero_ne_one this
end PI.Dv.Tr
