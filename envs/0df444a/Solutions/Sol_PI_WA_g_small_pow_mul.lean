-- Prove2me | solution 1 for PI.WA.g_small_pow_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:06:42.896802+00:00
-- url     : https://prove2.me/submissions/231d271c-55a6-41b5-96ae-69fc342ad50a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeakApproximationDVR_BigExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeakApproximationDVR_BigExistenceHolds
import Theorems.Thm_PI_WADVR_Sm_mono
import Theorems.Thm_PI_WADVR_Sm_mul
import Theorems.Thm_PI_WADVR_Sm_pow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WA
open PI.WADVR
variable {W Q : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Q]
  [Algebra W Q] [IsFractionRing W Q] {ϖ : W}
namespace PI.WA
theorem _root_.solution (hϖ : Irreducible ϖ) {q Y : Q} (hq : Sm Q ϖ 1 q) {m : ℤ} (hY : Sm Q ϖ m Y)
    (r : ℕ) (hr : 1 ≤ (r : ℤ) + m) : Sm Q ϖ 1 (q ^ r * Y) :=
  ((Sm.pow hϖ hq r).mul hϖ hY).mono hϖ (by push_cast; omega)
end PI.WA
