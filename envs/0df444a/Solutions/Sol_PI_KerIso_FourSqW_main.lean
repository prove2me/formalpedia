-- Prove2me | solution 1 for PI.KerIso.FourSqW.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:23:49.175032+00:00
-- url     : https://prove2.me/submissions/c8179aa8-ec4d-4f1b-9ee1-b61a56fac729

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FourSquareQuaternions_OrthogonalDiagonal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FourSquareQuaternions_QmapInjective
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FourSquareQuaternions_FourSqOfFromDiag
import Theorems.Thm_PI_KerIso_FourSqW_fourSq_of
import Theorems.Thm_PI_KerIso_FourSqW_from_diagonal
import Theorems.Thm_PI_KerIso_FourSqW_orthogonal_diagonal


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.KerIso PI.KerIso.FourSqW
namespace PI.KerIso.FourSqW
theorem _root_.solution : FourSq := fourSq_of orthogonal_diagonal from_diagonal
end PI.KerIso.FourSqW
