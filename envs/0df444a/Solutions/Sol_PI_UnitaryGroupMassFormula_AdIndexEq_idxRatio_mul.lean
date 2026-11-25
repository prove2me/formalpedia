-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.AdIndexEq.idxRatio_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:59:14.33665+00:00
-- url     : https://prove2.me/submissions/3edee157-eb97-46ef-b8ed-635b71cebc34

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_Commensurated
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_ModQEqOneOfMemNormalizer
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_idxRatio_eq_of_le
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_relIndex_inf_three_ne_zero
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_relIndex_self_ne_zero

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
theorem _root_.solution (A B C : Subgroup G)
    (hAB : B.relIndex A ≠ 0) (hAC : C.relIndex A ≠ 0) (hBA : A.relIndex B ≠ 0)
    (hBC : C.relIndex B ≠ 0) :
    idxRatio A B * idxRatio B C = idxRatio A C := by
  have hDA := relIndex_inf_three_ne_zero (relIndex_self_ne_zero A) hAB hAC
  have hDB := relIndex_inf_three_ne_zero hBA (relIndex_self_ne_zero B) hBC
  rw [idxRatio_eq_of_le A B (A ⊓ B ⊓ C) (le_trans inf_le_left inf_le_left)
      (le_trans inf_le_left inf_le_right) hDA,
    idxRatio_eq_of_le B C (A ⊓ B ⊓ C) (le_trans inf_le_left inf_le_right) inf_le_right hDB,
    idxRatio_eq_of_le A C (A ⊓ B ⊓ C) (le_trans inf_le_left inf_le_left) inf_le_right hDA,
    div_mul_div_comm, mul_comm ((A ⊓ B ⊓ C).relIndex A : ℚ),
    mul_div_mul_left _ _ (Nat.cast_ne_zero.mpr hDB)]
end PI.UnitaryGroupMassFormula.AdIndexEq
