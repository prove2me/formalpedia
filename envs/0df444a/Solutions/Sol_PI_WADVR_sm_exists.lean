-- Prove2me | solution 1 for PI.WADVR.sm_exists
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:01:05.088162+00:00
-- url     : https://prove2.me/submissions/4565131a-bc6b-4165-a1a7-a10709053afb

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
theorem _root_.solution (hϖ : Irreducible ϖ) (q : Q) : ∃ k : ℤ, Sm Q ϖ k q := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := W) q
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible hb0 hϖ
  refine ⟨-(n : ℤ), a * ((u : W)), ?_⟩
  have hbQ : algebraMap W Q b ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective W Q)).mpr hb0
  have hu' : algebraMap W Q b * algebraMap W Q (u : W) = algebraMap W Q ϖ ^ n := by
    rw [← map_mul, hu, map_pow]
  rw [zpow_neg, zpow_natCast, ← hu', map_mul]
  have hU : algebraMap W Q (u : W) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective W Q)).mpr u.ne_zero
  field_simp
end PI.WADVR
