-- Prove2me | solution 1 for PI.WADVR.Sm.pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:24:26.987065+00:00
-- url     : https://prove2.me/submissions/53af8391-de7d-404a-b2e3-51a7dfc7c663

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeakApproximationDVR_SmOneOfNotIsUnit
import Theorems.Thm_PI_WADVR_Sm_mul
import Theorems.Thm_PI_WADVR_Sm_zero
import Theorems.Thm_PI_WADVR_Sm_one

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
theorem _root_.solution (hϖ : Irreducible ϖ) {k : ℤ} {a : Q} (ha : Sm Q ϖ k a) (r : ℕ) :
    Sm Q ϖ (k * r) (a ^ r) := by
  induction r with
  | zero => simpa using (Sm.one (ϖ := ϖ) (Q := Q))
  | succ r ih =>
    have := ih.mul hϖ ha
    rw [pow_succ]
    convert this using 1
    push_cast; ring
end Sm
end PI.WADVR
