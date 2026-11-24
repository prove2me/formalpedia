-- Prove2me | solution 1 for PI.WADVR.one_add_of_sm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:19:53.897797+00:00
-- url     : https://prove2.me/submissions/19291085-09de-4434-922e-00f768ac1ab4

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
theorem _root_.solution (hϖ : Irreducible ϖ) {t : Q} (ht : Sm Q ϖ 1 t) :
    1 + t ≠ 0 ∧ Sm Q ϖ 0 (1 + t)⁻¹ := by
  obtain ⟨c, rfl⟩ := ht
  have hm : -(ϖ * c) ∈ nonunits W := by
    rw [← IsLocalRing.mem_maximalIdeal, Ideal.neg_mem_iff]
    exact Ideal.mul_mem_right _ _ ((IsLocalRing.mem_maximalIdeal _).mpr hϖ.not_isUnit)
  obtain ⟨u, hu⟩ := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ hm
  have he : (1 : Q) + algebraMap W Q ϖ ^ (1 : ℤ) * algebraMap W Q c = algebraMap W Q (u : W) := by
    rw [hu, zpow_one, sub_neg_eq_add, map_add, map_one, map_mul]
  have hU : algebraMap W Q (u : W) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective W Q)).mpr u.ne_zero
  refine ⟨he ▸ hU, ?_⟩
  rw [he]
  refine ⟨((u⁻¹ : Wˣ) : W), ?_⟩
  have h1 : algebraMap W Q (u : W) * algebraMap W Q ((u⁻¹ : Wˣ) : W) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  rw [zpow_zero, one_mul]
  exact (eq_inv_of_mul_eq_one_right h1).symm
end PI.WADVR
