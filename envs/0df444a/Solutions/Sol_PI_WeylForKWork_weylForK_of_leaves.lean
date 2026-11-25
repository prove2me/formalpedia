-- Prove2me | solution 1 for PI.WeylForKWork.weylForK_of_leaves
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:58:07.312903+00:00
-- url     : https://prove2.me/submissions/7948bb3a-6bcb-481d-b1d4-e2246e359490

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_WeylForKOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_TypePlOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_Assemble
import Theorems.Thm_PI_WeylForKWork_typeMi_of
import Theorems.Thm_PI_WeylForKWork_typePl_of
import Theorems.Thm_PI_WeylForKWork_weylForK_of_steps


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WeylForKWork
namespace PI.WeylForKWork
theorem _root_.solution (hB : Blocks) (hBD : BlockDiag) (hT : TorusWt) (hW : WtUniq) (hM : MinIrr)
    (hC : CDomRes) (hD : DimStep) (hF : FormulaStep) : PI.WeylForU → PI.WeylForK := by
  exact fun hU => weylForK_of_steps hB (typePl_of hB hBD hT hW hM hC) (typeMi_of hB hBD hT hW hM hC)
    hD hF hU
end PI.WeylForKWork
