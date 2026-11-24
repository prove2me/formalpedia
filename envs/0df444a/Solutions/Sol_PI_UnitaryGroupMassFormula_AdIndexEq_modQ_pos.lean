-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.AdIndexEq.modQ_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:56:08.699079+00:00
-- url     : https://prove2.me/submissions/fb024d67-30fd-4a20-854c-2da7596eead6

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
theorem _root_.solution (K : Subgroup G) (hK : Commensurated K) (x : G) : 0 < modQ K x := by
  unfold modQ
  exact div_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (hK x))) (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (hK x⁻¹)))
end PI.UnitaryGroupMassFormula.AdIndexEq
