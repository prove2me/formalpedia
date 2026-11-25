-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_finprod_iSup_algebraMap_6de04aaeab4a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:41:46.356607+00:00
-- url     : https://prove2.me/submissions/b0ead819-604f-4921-8f1e-fb0b12a8ca8c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CardEmbeddingsRestrict
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FieldChange
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_finprod_iSup_algebraMap_int_cb052d817af6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_hasFiniteMulSupport_iSup_place_6bf3c48ba8b2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_finprod_algebraMap_0cb43d4267e7

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
open NumberField Module
noncomputable section
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {ι : Type*} [Finite ι] {y : ι → K} (hy : y ≠ 0) :
    ∏ᶠ w : FinitePlace L, ⨆ i, w (algebraMap K L (y i)) =
      (∏ᶠ v : FinitePlace K, ⨆ i, v (y i)) ^ finrank K L := by
  obtain ⟨⟨b, hb⟩, hint⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 K)) y
  choose z hz using hint
  have hb0 : (b : K) ≠ 0 := by
    rw [Ne, RingOfIntegers.coe_eq_zero_iff]
    exact nonZeroDivisors.ne_zero hb
  have hzy : ∀ i, ((z i : 𝓞 K) : K) = (b : K) * y i := fun i ↦ by
    have h := hz i
    simp only [Algebra.smul_def] at h
    exact h
  have hz0 : z ≠ 0 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hy
    refine Function.ne_iff.mpr ⟨i, fun h ↦ hi ?_⟩
    have h1 : (b : K) * y i = 0 := by rw [← hzy i, h]; simp
    exact (mul_eq_zero.mp h1).resolve_left hb0
  have key := finprod_iSup_algebraMap_int (L := L) hz0
  have hsupK : ∀ v : FinitePlace K, ⨆ i, v (z i : K) = v (b : K) * ⨆ i, v (y i) := by
    intro v
    simp_rw [hzy, map_mul]
    exact (Real.mul_iSup_of_nonneg (apply_nonneg v _) _).symm
  have hsupL : ∀ w : FinitePlace L, ⨆ i, w (algebraMap K L (z i : K)) =
      w (algebraMap K L (b : K)) * ⨆ i, w (algebraMap K L (y i)) := by
    intro w
    simp_rw [hzy, map_mul]
    exact (Real.mul_iSup_of_nonneg (apply_nonneg w _) _).symm
  simp_rw [hsupK, hsupL] at key
  have hyL : (fun i ↦ algebraMap K L (y i)) ≠ 0 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hy
    exact Function.ne_iff.mpr ⟨i, (map_ne_zero _).mpr hi⟩
  rw [finprod_mul_distrib (FinitePlace.hasFiniteMulSupport ((map_ne_zero _).mpr hb0))
      (hasFiniteMulSupport_iSup_place hyL),
    finprod_mul_distrib (FinitePlace.hasFiniteMulSupport hb0) (hasFiniteMulSupport_iSup_place hy),
    mul_pow, finprod_algebraMap hb0] at key
  have hne : (∏ᶠ v : FinitePlace K, v (b : K)) ^ finrank K L ≠ 0 := by
    rw [FinitePlace.prod_eq_inv_abs_norm hb0]
    simp [hb0]
  exact mul_left_cancel₀ hne key
end GroundTheory.Heights₂.Heights
