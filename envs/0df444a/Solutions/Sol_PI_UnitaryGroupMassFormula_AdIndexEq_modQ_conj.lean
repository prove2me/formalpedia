-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.AdIndexEq.modQ_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:17:17.37516+00:00
-- url     : https://prove2.me/submissions/4933f842-0320-4849-a969-38593d8da022

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_Commensurated
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_ModQEqOneOfMemNormalizer
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_modQ_inv
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_modQ_pos
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
theorem _root_.solution (K : Subgroup G) (hK : Commensurated K) (x y : G) :
    modQ K (y * x * y⁻¹) = modQ K x := by
  rw [modQ_mul K hK, modQ_mul K hK, modQ_inv]
  have hy := (modQ_pos K hK y).ne'
  rw [mul_comm (modQ K y) (modQ K x), mul_assoc, mul_inv_cancel₀ hy, mul_one]
end PI.UnitaryGroupMassFormula.AdIndexEq
