-- Prove2me | solution 1 for PI.KerIso.FourSqW.tr_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:02:13.917385+00:00
-- url     : https://prove2.me/submissions/e48db74c-4d62-4756-b8d2-5324bf8b4cf8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FourSquareQuaternions_FourSqOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FourSquareQuaternions_OrthogonalDiagonal
import Theorems.Thm_PI_KerIso_FourSqW_trace_cj

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
theorem _root_.solution (cj : E ≃ₐ[ℚ] E) (hc : IsConj K cj) (x y : E) :
    algebraMap K E (Algebra.trace K E (y * cj x)) = cj (algebraMap K E (Algebra.trace K E (x * cj y))) := by
  rw [← trace_cj cj hc, map_mul cj, hc.1, mul_comm]
end PI.KerIso.FourSqW
