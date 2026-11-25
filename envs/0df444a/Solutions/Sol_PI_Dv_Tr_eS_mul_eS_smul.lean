-- Prove2me | solution 1 for PI.Dv.Tr.eS_mul_eS_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:03:56.962062+00:00
-- url     : https://prove2.me/submissions/ccf44129-67ed-42d0-8048-61c82e9d660c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_ESMulESOfNeZero
import Theorems.Thm_PI_Dv_Tr_phiS_one
import Theorems.Thm_PI_Dv_Tr_mul_eS
import Theorems.Thm_PI_Dv_Tr_tau_eS_scalar

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
theorem _root_.solution (T : GoodSet K G) (s t : T.S) : ∃ c : K, eS T s * eS T t = c • eS T t := by
  obtain ⟨c, hc⟩ := tau_eS_scalar T s t
  exact ⟨c, by rw [mul_eS, hc, map_smul, phiS_one]⟩
end PI.Dv.Tr
