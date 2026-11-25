-- Prove2me | solution 1 for PI.GGMirBoundW.mirabolicBound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:12:18.552827+00:00
-- url     : https://prove2.me/submissions/4500ac34-007f-4c9f-a504-204ecb45f8e8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirabolicBound_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirabolicBound_LastRowMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirabolicBound_RowExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirabolicBound_CharSumOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirabolicBound_CardNonzero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirabolicBound_MirabolicBound
import Theorems.Thm_PI_GGMirBoundW_baseProp
import Theorems.Thm_PI_GGMirBoundW_blkFacts
import Theorems.Thm_PI_GGMirBoundW_charOrth
import Theorems.Thm_PI_GGMirBoundW_colFacts
import Theorems.Thm_PI_GGMirBoundW_conjCol
import Theorems.Thm_PI_GGMirBoundW_mirabolicBound_of_steps
import Theorems.Thm_PI_GGMirBoundW_rowExists
import Theorems.Thm_PI_GGMirBoundW_sepLemma
import Theorems.Thm_PI_GGMirBoundW_stepOf


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.GGMirBoundW
namespace PI.GGMirBoundW
theorem _root_.solution : Formalism.L2.SG.GGMirabolic.MirabolicBound :=
  mirabolicBound_of_steps baseProp stepOf blkFacts colFacts conjCol rowExists charOrth sepLemma
end PI.GGMirBoundW
