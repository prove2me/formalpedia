-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.AdIndexEq.dIdx_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:36:47.261209+00:00
-- url     : https://prove2.me/submissions/0a5671c1-dcad-4686-8779-bd4618f13846

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_Commensurated
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_ModQEqOneOfMemNormalizer
import Theorems.Thm_P2M_PI_UnitaryGroupMassFormula_AdIndexEq_map_conj_one__c177881babcc

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
theorem _root_.solution (K : Subgroup G) : dIdx K 1 = 1 := by
  unfold dIdx
  rw [map_conj_one', Subgroup.relIndex_self]
end PI.UnitaryGroupMassFormula.AdIndexEq
