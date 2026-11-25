-- Prove2me | solution 1 for PI.WADVR.sm_one_of_not_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:18:50.295992+00:00
-- url     : https://prove2.me/submissions/47b85aee-1008-4cee-8d12-e61e7788ed0f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeakApproximationDVR_SmOneOfNotIsUnit
import Theorems.Thm_PI_WADVR_sm_one_of_mem

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
theorem _root_.solution (hϖ : Irreducible ϖ) {w : W} (hw : ¬ IsUnit w) :
    Sm Q ϖ 1 (algebraMap W Q w) :=
  sm_one_of_mem hϖ ((IsLocalRing.mem_maximalIdeal _).mpr hw)
end PI.WADVR
