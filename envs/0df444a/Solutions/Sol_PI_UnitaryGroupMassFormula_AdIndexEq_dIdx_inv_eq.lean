-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.AdIndexEq.dIdx_inv_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:36:44.028521+00:00
-- url     : https://prove2.me/submissions/8d5db5f4-2988-46af-92d8-22614cdd6400

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_Commensurated
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_ModQEqOneOfMemNormalizer
import Theorems.Thm_P2M_PI_UnitaryGroupMassFormula_AdIndexEq_map_conj_mul__880dfd7f91e9
import Theorems.Thm_P2M_PI_UnitaryGroupMassFormula_AdIndexEq_map_conj_one__c177881babcc
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


section
noncomputable section
namespace PI.UnitaryGroupMassFormula.AdIndexEq
section Delta
variable {G : Type} [Group G]
private theorem relIndex_map_of_injective (X Y : Subgroup G) (f : G →* G) (hf : Function.Injective f) :
    (X.map f).relIndex (Y.map f) = X.relIndex Y := by
  rw [← Subgroup.relIndex_comap, Subgroup.comap_map_eq_self_of_injective hf]
end Delta
end PI.UnitaryGroupMassFormula.AdIndexEq
end
end

set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.AdIndexEq
variable {G : Type} [Group G]
namespace PI.UnitaryGroupMassFormula.AdIndexEq
theorem _root_.solution (K : Subgroup G) (x : G) :
    dIdx K x⁻¹ = K.relIndex (K.map (MulAut.conj x).toMonoidHom) := by
  unfold dIdx
  rw [← relIndex_map_of_injective _ _ (MulAut.conj x).toMonoidHom (by intro a b h; simpa using h),
    map_conj_mul', mul_inv_cancel, map_conj_one']
end PI.UnitaryGroupMassFormula.AdIndexEq
