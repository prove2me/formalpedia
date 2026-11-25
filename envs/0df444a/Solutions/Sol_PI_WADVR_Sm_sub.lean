-- Prove2me | solution 1 for PI.WADVR.Sm.sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:08:50.419053+00:00
-- url     : https://prove2.me/submissions/7983fafa-f933-4846-b01c-c63fe977f7fc

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeakApproximationDVR_SmOneOfNotIsUnit
import Theorems.Thm_PI_WADVR_Sm_add
import Theorems.Thm_PI_WADVR_Sm_neg

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
theorem _root_.solution {k : ℤ} {a b : Q} (ha : Sm Q ϖ k a) (hb : Sm Q ϖ k b) : Sm Q ϖ k (a - b) := by
  rw [sub_eq_add_neg]; exact ha.add hb.neg
end Sm
end PI.WADVR
