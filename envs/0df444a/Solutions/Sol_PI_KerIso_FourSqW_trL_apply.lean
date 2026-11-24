-- Prove2me | solution 1 for PI.KerIso.FourSqW.trL_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:47:20.869643+00:00
-- url     : https://prove2.me/submissions/8ee175f4-b64f-4698-8d34-30192a2cb635

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FourSquareQuaternions_FourSqOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FourSquareQuaternions_OrthogonalDiagonal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Module
open PI PI.KerIso PI.KerIso.FourSqW
variable {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]
namespace PI.KerIso.FourSqW
theorem _root_.solution (cj : E ≃ₐ[ℚ] E) (y x : E) : trL (K := K) cj y x = Algebra.trace K E (x * cj y) := rfl
end PI.KerIso.FourSqW
