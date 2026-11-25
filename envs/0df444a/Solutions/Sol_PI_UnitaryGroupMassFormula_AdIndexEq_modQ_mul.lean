-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.AdIndexEq.modQ_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:22:27.937986+00:00
-- url     : https://prove2.me/submissions/b3fb35a2-7c7c-46c0-b73c-f0ee38c04fcf

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_Commensurated
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_ModQEqOneOfMemNormalizer
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_idxRatio_mul
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_idxRatio_map
import Theorems.Thm_P2M_PI_UnitaryGroupMassFormula_AdIndexEq_map_conj_mul__880dfd7f91e9
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_relIndex_conj_conj_ne_zero
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_relIndex_conj_right_ne_zero
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
theorem _root_.solution (K : Subgroup G) (hK : Commensurated K) (x y : G) :
    modQ K (x * y) = modQ K x * modQ K y := by
  rw [modQ_eq_idxRatio, modQ_eq_idxRatio, modQ_eq_idxRatio,
    ← idxRatio_map K (K.map (MulAut.conj y).toMonoidHom) (MulAut.conj x).toMonoidHom
      (by intro a b h; simpa using h), map_conj_mul']
  exact (idxRatio_mul K (K.map (MulAut.conj x).toMonoidHom) (K.map (MulAut.conj (x * y)).toMonoidHom)
    (hK x) (hK (x * y)) (relIndex_conj_right_ne_zero K hK x)
    (relIndex_conj_conj_ne_zero K hK (x * y) x)).symm
end PI.UnitaryGroupMassFormula.AdIndexEq
