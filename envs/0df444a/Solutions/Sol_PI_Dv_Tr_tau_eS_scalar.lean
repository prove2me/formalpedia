-- Prove2me | solution 1 for PI.Dv.Tr.tau_eS_scalar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:56:47.143651+00:00
-- url     : https://prove2.me/submissions/45a88604-9910-4d69-9637-9020b97d8080

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_ESMulESOfNeZero
import Theorems.Thm_PI_Dv_Tr_eS_comm
import Theorems.Thm_PI_Dv_Tr_scalar_of_comm

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
theorem _root_.solution (T : GoodSet K G) (s t : T.S) : ∃ c : K, (T.tau t).asAlgebraHom (eS T s) = c • 1 := by
  apply scalar_of_comm
  intro g
  rw [← Representation.asAlgebraHom_of, ← map_mul, ← map_mul, eS_comm]
end PI.Dv.Tr
