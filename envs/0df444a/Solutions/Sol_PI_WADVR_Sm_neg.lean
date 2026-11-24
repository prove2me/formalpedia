-- Prove2me | solution 1 for PI.WADVR.Sm.neg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:04:44.620458+00:00
-- url     : https://prove2.me/submissions/3a31587d-4d38-480d-a158-2bba23dc11d6

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
theorem _root_.solution {k : ℤ} {a : Q} (ha : Sm Q ϖ k a) : Sm Q ϖ k (-a) := by
  obtain ⟨c, rfl⟩ := ha
  exact ⟨-c, by rw [map_neg]; ring⟩
end Sm
end PI.WADVR
