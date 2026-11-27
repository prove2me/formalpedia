-- Prove2me | solution 1 for PI.WADVR.Sm.of_toNat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:19:29.531885+00:00
-- url     : https://prove2.me/submissions/a26378a4-489c-46e0-a27c-8c909bc7bcbb

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeakApproximationDVR_SmOneOfNotIsUnit
import Theorems.Thm_PI_WADVR_Sm_mono

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WADVR
variable {W Q : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Q]
  [Algebra W Q] [IsFractionRing W Q]
variable {ϖ : W}
namespace PI.WADVR
namespace Sm
theorem _root_.solution (hϖ : Irreducible ϖ) {k : ℤ} {a : Q} (ha : Sm Q ϖ (k.toNat : ℤ) a) :
    Sm Q ϖ k a :=
  ha.mono hϖ (Int.self_le_toNat k)
end Sm
end PI.WADVR
