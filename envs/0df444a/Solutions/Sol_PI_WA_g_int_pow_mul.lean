-- Prove2me | solution 1 for PI.WA.g_int_pow_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:04:46.515988+00:00
-- url     : https://prove2.me/submissions/4e70eade-fc84-4d88-87f7-06d2f15176ef

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
theorem _root_.solution (hϖ : Irreducible ϖ) {q Y : Q} (hq : Sm Q ϖ 0 q) (hY : Sm Q ϖ 1 Y) (r : ℕ) :
    Sm Q ϖ 1 (q ^ r * Y) := by
  exact ((Sm.pow hϖ hq r).mul hϖ hY).mono hϖ (by push_cast; omega)
end PI.WA
