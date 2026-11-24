-- Prove2me | solution 1 for PI.WADVR.Sm.mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:24.562713+00:00
-- url     : https://prove2.me/submissions/3c031fc7-726b-4d98-8b88-bb1b4b4b5d57

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeakApproximationDVR_SmOneOfNotIsUnit
import Theorems.Thm_PI_WADVR_alg_ne_zero

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
theorem _root_.solution (hϖ : Irreducible ϖ) {k l : ℤ} {a b : Q} (ha : Sm Q ϖ k a) (hb : Sm Q ϖ l b) :
    Sm Q ϖ (k + l) (a * b) := by
  obtain ⟨c, rfl⟩ := ha
  obtain ⟨d, rfl⟩ := hb
  refine ⟨c * d, ?_⟩
  rw [zpow_add₀ (alg_ne_zero hϖ), map_mul]
  ring
end Sm
end PI.WADVR
