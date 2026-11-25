-- Prove2me | solution 1 for PI.WADVR.big_of_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:32:55.698802+00:00
-- url     : https://prove2.me/submissions/20cb2f8c-431d-4ed8-bdee-1dd85ca0e170

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeakApproximationDVR_SmOneOfNotIsUnit
import Theorems.Thm_PI_WADVR_sm_one_of_not_isUnit

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
theorem _root_.solution (hϖ : Irreducible ϖ) {q : Q} (hq : q ∉ Set.range (algebraMap W Q)) :
    q ≠ 0 ∧ Sm Q ϖ 1 q⁻¹ := by
  have hq0 : q ≠ 0 := by rintro rfl; exact hq ⟨0, by simp⟩
  refine ⟨hq0, ?_⟩
  rcases ValuationRing.isInteger_or_isInteger W q with ⟨w, hw⟩ | ⟨w, hw⟩
  · exact absurd ⟨w, hw⟩ hq
  · refine hw ▸ sm_one_of_not_isUnit hϖ ?_
    rintro ⟨u, rfl⟩
    apply hq
    refine ⟨((u⁻¹ : Wˣ) : W), ?_⟩
    have h1 : algebraMap W Q (u : W) * algebraMap W Q ((u⁻¹ : Wˣ) : W) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    rw [hw] at h1
    field_simp at h1
    exact h1
end PI.WADVR
