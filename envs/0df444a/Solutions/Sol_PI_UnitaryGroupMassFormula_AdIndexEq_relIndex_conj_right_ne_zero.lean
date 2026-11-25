-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.AdIndexEq.relIndex_conj_right_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:40:45.588605+00:00
-- url     : https://prove2.me/submissions/754e15b5-3dbb-4c2d-811e-3913611b38d2

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_Commensurated
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_ModQEqOneOfMemNormalizer
import Theorems.Thm_P2M_PI_UnitaryGroupMassFormula_AdIndexEq_map_conj_one__c177881babcc
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_relIndex_conj_conj_ne_zero

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
theorem _root_.solution (K : Subgroup G) (hK : Commensurated K) (a : G) :
    K.relIndex (K.map (MulAut.conj a).toMonoidHom) ≠ 0 := by
  have h := relIndex_conj_conj_ne_zero K hK 1 a
  rwa [map_conj_one'] at h
end PI.UnitaryGroupMassFormula.AdIndexEq
