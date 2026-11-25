-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.AdIndexEq.modQ_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:34:05.782259+00:00
-- url     : https://prove2.me/submissions/2b7fe57f-b2f1-4e6a-933f-d978549a7625

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_Commensurated
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_ModQEqOneOfMemNormalizer
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_modQ_one
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_modQ_mul

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
theorem _root_.solution (K : Subgroup G) (hK : Commensurated K) (x : G) (m : ℕ) :
    modQ K (x ^ m) = (modQ K x) ^ m := by
  induction m with
  | zero => rw [pow_zero, pow_zero, modQ_one]
  | succ m ih => rw [pow_succ, modQ_mul K hK, ih, pow_succ]
end PI.UnitaryGroupMassFormula.AdIndexEq
