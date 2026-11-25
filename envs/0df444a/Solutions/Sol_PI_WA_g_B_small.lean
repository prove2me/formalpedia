-- Prove2me | solution 1 for PI.WA.g_B_small
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:04:38.912456+00:00
-- url     : https://prove2.me/submissions/5aa6b667-341d-4d1a-ac8b-370941411e6c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeakApproximationDVR_BigExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeakApproximationDVR_BigExistenceHolds
import Theorems.Thm_PI_WADVR_Sm_mono
import Theorems.Thm_PI_WADVR_Sm_mul
import Theorems.Thm_PI_WADVR_Sm_pow
import Theorems.Thm_PI_WADVR_one_add_of_sm


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
theorem _root_.solution (hϖ : Irreducible ϖ) {q Y : Q} (hq : Sm Q ϖ 1 q) {m : ℤ} (hY : Sm Q ϖ m Y) {r : ℕ}
    (hr : 1 ≤ r) (hrm : 1 ≤ (r : ℤ) + m) : Sm Q ϖ 1 (q ^ r * (1 + q ^ r)⁻¹ * Y) := by
  have hqr := Sm.pow hϖ hq r
  obtain ⟨-, hinv⟩ := one_add_of_sm hϖ (hqr.mono hϖ (by push_cast; omega))
  exact ((hqr.mul hϖ hinv).mul hϖ hY).mono hϖ (by push_cast; omega)
end PI.WA
