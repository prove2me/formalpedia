-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.AdIndexEq.modQ_eq_one_of_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:43:41.964559+00:00
-- url     : https://prove2.me/submissions/baf3c4f5-08a5-4f57-a3fd-4d58ecb7caf9

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_Commensurated
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_ModQEqOneOfMemNormalizer
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_modQ_pos
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_modQ_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.AdIndexEq
variable {G : Type} [Group G]
namespace PI.UnitaryGroupMassFormula.AdIndexEq
theorem _root_.solution (K : Subgroup G) (hK : Commensurated K) (x : G) {m : ℕ} (hm : m ≠ 0)
    (h : modQ K (x ^ m) = 1) : modQ K x = 1 := by
  rw [modQ_pow K hK] at h
  exact (pow_eq_one_iff_of_nonneg (modQ_pos K hK x).le hm).mp h
end PI.UnitaryGroupMassFormula.AdIndexEq
