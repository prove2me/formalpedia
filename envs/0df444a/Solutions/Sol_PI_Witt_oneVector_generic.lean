-- Prove2me | solution 1 for PI.Witt.oneVector_generic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:14:16.066569+00:00
-- url     : https://prove2.me/submissions/3905802e-bcb2-48a7-b152-3e075db06700

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittDecomposition_Anisotropic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittDecomposition_OneVector
import Theorems.Thm_PI_Witt_qrefl_isometry

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.Witt
variable {K V : Type} [Field K] [StarRing K] [CharZero K] [AddCommGroup V] [Module K V]
  (B : V →ₗ⋆[K] V →ₗ[K] K)
namespace PI.Witt
theorem _root_.solution (hB : ∀ x y, star (B x y) = B y x) (x y : V) (hxy : B x x = B y y)
    (ha : B (x - y) x ≠ 0) :
    ∃ g : V ≃ₗ[K] V, (∀ z w, B (g z) (g w) = B z w) ∧ g x = y ∧
      ∀ z, B x z = 0 → B y z = 0 → g z = z := by
  have hv : B (x - y) (x - y) = B (x - y) x + star (B (x - y) x) := by
    rw [hB]
    simp only [map_sub, LinearMap.sub_apply]
    rw [← hxy]
    ring
  refine ⟨qreflEquiv B (x - y) (B (x - y) x) ha hv,
    fun z w => qrefl_isometry B hB (x - y) _ ha hv z w, ?_, fun z hz1 hz2 => ?_⟩
  · show qrefl B (x - y) (B (x - y) x) x = y
    rw [qrefl_apply, inv_mul_cancel₀ ha, one_smul, sub_sub_cancel]
  · show qrefl B (x - y) (B (x - y) x) z = z
    rw [qrefl_apply]
    simp only [map_sub, LinearMap.sub_apply, hz1, hz2, sub_zero, mul_zero, zero_smul]
end PI.Witt
