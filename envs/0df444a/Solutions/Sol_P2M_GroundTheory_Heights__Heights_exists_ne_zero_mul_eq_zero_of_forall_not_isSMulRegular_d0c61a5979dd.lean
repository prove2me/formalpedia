-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_exists_ne_zero_mul_eq_zero_of_forall_not_isSMulRegular_d0c61a5979dd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:32:14.547022+00:00
-- url     : https://prove2.me/submissions/4bf1ad63-1683-4571-bf67-578433c2a7c0

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularUFDLocalization
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_AuslanderBuchsbaumDepthBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open IsLocalRing CategoryTheory RingTheory.Sequence Ideal
open scoped Pointwise
universe u
variable {R : Type u} [CommRing R]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution [IsLocalRing R] [IsNoetherianRing R]
    (h : ∀ y ∈ maximalIdeal R, ¬ IsSMulRegular R y) :
    ∃ s : R, s ≠ 0 ∧ ∀ a ∈ maximalIdeal R, a * s = 0 := by
  have hmk : ∀ y : R, y • (1 : R ⧸ maximalIdeal R) = Ideal.Quotient.mk (maximalIdeal R) y := fun y ↦ by
    rw [Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq]
  have hns : ¬ Subsingleton ((R ⧸ maximalIdeal R) →ₗ[R] R) := by
    rw [IsSMulRegular.subsingleton_linearMap_iff]
    rintro ⟨r, hr, hreg⟩
    refine h r ?_ hreg
    have h1 := Module.mem_annihilator.mp hr (1 : R ⧸ maximalIdeal R)
    rwa [hmk, Ideal.Quotient.eq_zero_iff_mem] at h1
  rw [not_subsingleton_iff_nontrivial] at hns
  obtain ⟨f, hf⟩ := exists_ne (0 : (R ⧸ maximalIdeal R) →ₗ[R] R)
  refine ⟨f 1, fun h0 ↦ hf (LinearMap.ext fun y ↦ ?_), fun a ha ↦ ?_⟩
  · obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← hmk, map_smul, h0, smul_zero, LinearMap.zero_apply]
  · rw [← smul_eq_mul, ← map_smul, hmk, Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]
end GroundTheory.Heights₂.Heights
