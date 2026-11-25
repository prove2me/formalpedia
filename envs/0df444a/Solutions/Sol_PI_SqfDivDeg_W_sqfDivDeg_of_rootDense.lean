-- Prove2me | solution 1 for PI.SqfDivDeg.W.sqfDivDeg_of_rootDense
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:41:05.167148+00:00
-- url     : https://prove2.me/submissions/59b73ead-cfa4-4b9f-af6d-8dd84f7bd9f0

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeDivisorDegree_SqfDivDegOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeDivisorDegree_FibreNonempty
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeDivisorDegree_Assemble
import Theorems.Thm_PI_SqfDivDeg_W_mainCount
import Theorems.Thm_PI_SqfDivDeg_W_sqfDivDeg_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.SqfDivDeg PI.SqfDivDeg.W
namespace PI.SqfDivDeg.W
theorem _root_.solution (hA : RootDense) : PI.SqfDivDeg.Claim :=
  sqfDivDeg_of hA mainCount
end PI.SqfDivDeg.W
