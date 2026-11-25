-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.relIdx_map_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:58:46.142816+00:00
-- url     : https://prove2.me/submissions/64e4c19e-25df-4a16-a4a7-796b589b7326

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RelIdxNeZeroOfLeLeft
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_smulHom_inj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
namespace PI.UnitaryGroupMassFormula.UnimodLocStd
theorem _root_.solution {w : ℂ} (hw : w ≠ 0) (A B : AddSubgroup V) :
    (A.map (smulHom w)).relIndex (B.map (smulHom w)) = A.relIndex B := by
  exact AddSubgroup.relIndex_map_map_of_injective A B (smulHom_inj hw)
end PI.UnitaryGroupMassFormula.UnimodLocStd
