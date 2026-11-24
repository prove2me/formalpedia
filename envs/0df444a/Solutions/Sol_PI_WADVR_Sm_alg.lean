-- Prove2me | solution 1 for PI.WADVR.Sm.alg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:21:07.815666+00:00
-- url     : https://prove2.me/submissions/21b0aee7-bacd-4de0-a214-a87d42dc5d8b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeakApproximationDVR_SmOneOfNotIsUnit

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
theorem _root_.solution (w : W) : Sm Q ϖ 0 (algebraMap W Q w) := ⟨w, by simp⟩
end Sm
end PI.WADVR
