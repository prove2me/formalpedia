-- Prove2me | solution 1 for PI.LocDualGen.Of.locDualGen_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:22:30.54293+00:00
-- url     : https://prove2.me/submissions/60c1e33c-7356-430a-b7c2-a5eca0e76e68

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocDualGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_PsiTower
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_AddCharKernel
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_FpDual
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_EpSelfDual
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_LocDualGenOf
import Theorems.Thm_PI_LocDualGen_EpG_quadraticSelfDual
import Theorems.Thm_PI_LocDualGen_FpD_existsDifferentGenerator
import Theorems.Thm_PI_LocDualGen_Psi_addCharKernel
import Theorems.Thm_PI_LocDualGen_Top_stmt_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.LocDualGen PI.LocDualGen.Of
namespace PI.LocDualGen.Of
theorem _root_.solution (h : PI.LocDualGen.W.FpDualUnram) : PI.LocDualGen.Stmt :=
  PI.LocDualGen.Top.stmt_of PI.LocDualGen.Psi.addCharKernel PI.LocDualGen.FpD.existsDifferentGenerator h
    PI.LocDualGen.EpG.quadraticSelfDual
end PI.LocDualGen.Of
