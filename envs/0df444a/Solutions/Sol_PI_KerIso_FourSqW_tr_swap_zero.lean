-- Prove2me | solution 1 for PI.KerIso.FourSqW.tr_swap_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:07:45.211184+00:00
-- url     : https://prove2.me/submissions/c4b794b0-29a4-4bba-a7ab-7e7223ed0957

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FourSquareQuaternions_FourSqOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FourSquareQuaternions_OrthogonalDiagonal
import Theorems.Thm_PI_KerIso_FourSqW_tr_swap

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
theorem _root_.solution (cj : E ≃ₐ[ℚ] E) (hc : IsConj K cj) (x y : E)
    (h : Algebra.trace K E (x * cj y) = 0) : Algebra.trace K E (y * cj x) = 0 := by
  apply (algebraMap K E).injective
  rw [tr_swap cj hc, h, map_zero, map_zero]
end PI.KerIso.FourSqW
