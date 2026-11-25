-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.AdIndexEq.modQ_eq_idxRatio
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:08:43.839647+00:00
-- url     : https://prove2.me/submissions/601e7492-8823-4145-bb9c-f0a5566b321e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_Commensurated
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_ModQEqOneOfMemNormalizer
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_dIdx_inv_eq

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
theorem _root_.solution (K : Subgroup G) (x : G) :
    modQ K x = idxRatio K (K.map (MulAut.conj x).toMonoidHom) := by
  unfold modQ idxRatio
  rw [dIdx_inv_eq]
  rfl
end PI.UnitaryGroupMassFormula.AdIndexEq
