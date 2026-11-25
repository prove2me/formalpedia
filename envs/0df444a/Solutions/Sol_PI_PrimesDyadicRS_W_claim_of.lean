-- Prove2me | solution 1 for PI.PrimesDyadicRS.W.claim_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:03:38.806212+00:00
-- url     : https://prove2.me/submissions/bc8a4851-f085-4771-aa47-5c4d62a11c08

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PrimesDyadicRS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_ThetaDiff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_PsiLowerBoundHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_FloorHalf
import Theorems.Thm_PI_PrimesDyadicRS_W_small_of
import Theorems.Thm_PI_PrimesDyadicRS_W_large_of

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.PrimesDyadicRS PI.PrimesDyadicRS.W
namespace PI.PrimesDyadicRS.W
theorem _root_.solution (hS : SmallNat) (hT : ThetaDiff) (hP : PsiTheta) (hR : RealIneq) :
    PI.PrimesDyadicRS.Claim := by
  intro y hy
  rcases lt_or_ge y 65536 with h | h
  · exact small_of hS y hy h
  · exact large_of hT hP hR y h
end PI.PrimesDyadicRS.W
