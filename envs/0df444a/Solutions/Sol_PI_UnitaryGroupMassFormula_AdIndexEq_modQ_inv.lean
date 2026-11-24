-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.AdIndexEq.modQ_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:56:02.724959+00:00
-- url     : https://prove2.me/submissions/c5eb83ae-ad53-44ae-a9d5-6ff550362f40

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
theorem _root_.solution (K : Subgroup G) (x : G) : modQ K x⁻¹ = (modQ K x)⁻¹ := by
  unfold modQ
  rw [inv_inv, inv_div]
end PI.UnitaryGroupMassFormula.AdIndexEq
