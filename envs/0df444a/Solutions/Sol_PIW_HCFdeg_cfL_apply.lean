-- Prove2me | solution 1 for PIW.HCFdeg.cfL_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:22:10.936804+00:00
-- url     : https://prove2.me/submissions/4a5f754b-ae27-47a7-a9f3-cd8360249d04

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_FormalDegreeFromOrthogonality
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_IntegrableCf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.HCFdeg
open MeasureTheory
open scoped InnerProductSpace ComplexConjugate
variable {G : Type} [Group G] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
namespace PIW.HCFdeg
theorem _root_.solution (π : G →* (H →L[ℂ] H)) (w v : H) : cfL π w v = cf π v w := rfl
end PIW.HCFdeg
