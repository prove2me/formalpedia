-- Prove2me | solution 1 for PI.WADVR.small_one_add_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:04:20.355796+00:00
-- url     : https://prove2.me/submissions/a855d1c2-7508-4ab7-9d0c-fea93aa4ca07

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeakApproximationDVR_SmOneOfNotIsUnit
import Theorems.Thm_PI_WADVR_Sm_mul
import Theorems.Thm_PI_WADVR_Sm_mono
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
open PI PI.WADVR
variable {W Q : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Q]
  [Algebra W Q] [IsFractionRing W Q]
variable {ϖ : W}
namespace PI.WADVR
theorem _root_.solution (hϖ : Irreducible ϖ) {q : Q} (h : Sm Q ϖ 1 q) {r : ℕ} (hr : 1 ≤ r) :
    1 + q ^ r ≠ 0 ∧ Sm Q ϖ r (q ^ r * (1 + q ^ r)⁻¹) := by
  have ht : Sm Q ϖ r (q ^ r) := by simpa using h.pow hϖ r
  obtain ⟨h1, h2⟩ := one_add_of_sm hϖ (ht.mono hϖ (by exact_mod_cast hr))
  refine ⟨h1, ?_⟩
  simpa using ht.mul hϖ h2
end PI.WADVR
