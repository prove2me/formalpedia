-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.AdIndexEq.relIndex_self_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:37:16.468843+00:00
-- url     : https://prove2.me/submissions/68bd9384-e68f-4269-af97-994b45dedfc7

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_Commensurated
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_ModQEqOneOfMemNormalizer

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
theorem _root_.solution (A : Subgroup G) : A.relIndex A ≠ 0 := by
  rw [Subgroup.relIndex_self]
  exact one_ne_zero
end PI.UnitaryGroupMassFormula.AdIndexEq
