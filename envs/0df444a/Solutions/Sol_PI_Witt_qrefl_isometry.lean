-- Prove2me | solution 1 for PI.Witt.qrefl_isometry
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:00:31.843399+00:00
-- url     : https://prove2.me/submissions/e6d7851d-4e6c-46ea-84a0-35669983d039

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittDecomposition_Anisotropic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittDecomposition_OneVector

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
theorem _root_.solution (hB : ∀ x y, star (B x y) = B y x) (v : V) (a : K) (ha : a ≠ 0)
    (hv : B v v = a + star a) (z w : V) :
    B (qrefl B v a z) (qrefl B v a w) = B z w := by
  have ha' : star a ≠ 0 := star_ne_zero.2 ha
  have key : ∀ p q r : K, p - a⁻¹ * q * r - (star a)⁻¹ * r * q +
      (star a)⁻¹ * r * (a⁻¹ * q) * (a + star a) = p := by
    intro p q r
    field_simp
    ring
  rw [qrefl_apply, qrefl_apply]
  simp only [map_sub, map_smulₛₗ, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
    map_smul, starRingEnd_apply, RingHom.id_apply, star_mul', star_inv₀, hB, hv]
  linear_combination key (B z w) (B v w) (B z v)
end PI.Witt
