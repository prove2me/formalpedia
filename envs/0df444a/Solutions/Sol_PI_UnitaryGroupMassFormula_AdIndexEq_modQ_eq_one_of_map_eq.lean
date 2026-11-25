-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.AdIndexEq.modQ_eq_one_of_map_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:19:30.654815+00:00
-- url     : https://prove2.me/submissions/2b61e471-20b5-4c3f-b656-9a74bec12b8d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_Commensurated
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_ModQEqOneOfMemNormalizer
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_modQ_eq_idxRatio
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.AdIndexEq
variable {G : Type} [Group G]
namespace PI.UnitaryGroupMassFormula.AdIndexEq
theorem _root_.solution (K : Subgroup G) (x : G)
    (h : K.map (MulAut.conj x).toMonoidHom = K) : modQ K x = 1 := by
  rw [modQ_eq_idxRatio, h]
  unfold idxRatio
  simp [Subgroup.relIndex_self]
end PI.UnitaryGroupMassFormula.AdIndexEq
