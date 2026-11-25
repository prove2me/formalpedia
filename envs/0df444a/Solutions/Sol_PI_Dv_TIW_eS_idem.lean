-- Prove2me | solution 1 for PI.Dv.TIW.eS_idem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:05:37.12771+00:00
-- url     : https://prove2.me/submissions/d00ad433-4ac2-498b-a226-c7e223778dd8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_TauCentralScalar
import Theorems.Thm_PI_Dv_TIW_theta_one
import Theorems.Thm_PI_Dv_TIW_mul_eS
import Theorems.Thm_PI_Dv_TIW_tau_eS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.TIW
open PI.Dv
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G] (T : GoodSet K G) (s : T.S)
namespace PI.Dv.TIW
theorem _root_.solution [CharZero K] : eS T s * eS T s = eS T s := by
  rw [mul_eS, tau_eS, theta_one]
end PI.Dv.TIW
