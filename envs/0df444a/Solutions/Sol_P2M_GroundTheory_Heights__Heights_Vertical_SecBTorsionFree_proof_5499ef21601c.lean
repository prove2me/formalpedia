-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_SecBTorsionFree_proof_5499ef21601c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:57:15.604531+00:00
-- url     : https://prove2.me/submissions/b9228d6a-58c9-44c5-a74a-2c93e7e323b1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSecBTorsionFree
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_secAlg_const_mul_eq_zero_46947a55642f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_dvd_pow_of_ne_zero_of_not_isUnit_81bea8ad7a4b

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial NumberField IsDedekindDomain
noncomputable section
namespace GroundTheory.Heights₂.Heights.Vertical
namespace SecBTorsionFree
theorem _root_.solution (h1 : ParDVRIsDVR.Statement) : SecBTorsionFree.Statement := by
  intro K _ _ n e I v hI r b hr hrb
  have := h1 K e n v
  have := hI.isPrime
  have hP : (integralModel I).IsPrime := by
    unfold integralModel
    infer_instance
  have hQ : ∀ a : 𝓞 K, C a ∈ integralModel I → a = 0 := by
    intro a ha
    by_contra h
    rw [integralModel, Ideal.mem_comap, map_C] at ha
    have hne : algebraMap (𝓞 K) K a ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr h
    exact hI.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ ha ((isUnit_iff_ne_zero.mpr hne).map C))
  obtain ⟨c, hcv, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  have hS0 : (parPrime e n v).primeCompl ≤ nonZeroDivisors (MvPolynomial (Par e n) (𝓞 K)) :=
    le_nonZeroDivisors_of_noZeroDivisors fun h => h (Ideal.zero_mem _)
  have hc'0 : algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v) (C c) ≠ 0 := by
    intro h0
    have h2 := IsLocalization.injective (ParDVR e n v) hS0 (h0.trans (map_zero _).symm)
    exact hc0 (C_injective (Par e n) (𝓞 K) (h2.trans (map_zero C).symm))
  have hc'u : ¬IsUnit (algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v) (C c)) := fun hu =>
    ((IsLocalization.AtPrime.isUnit_to_map_iff (ParDVR e n v) (parPrime e n v) (C c)).mp hu)
      (Ideal.mem_map_of_mem C hcv)
  obtain ⟨k, q, hq⟩ := dvd_pow_of_ne_zero_of_not_isUnit hr hc'0 hc'u
  have hmodel : modelR e I v = chartModel e (ParDVR e n v) (integralModel I) := by
    rw [modelR, chartModel, IsScalarTower.algebraMap_eq (𝓞 K) (MvPolynomial (Par e n) (𝓞 K))
      (ParDVR e n v), MvPolynomial.algebraMap_eq]
  have hrb' : algebraMap (ParDVR e n v) (SecB e I v) r * b = 0 := (Algebra.smul_def r b).symm.trans hrb
  refine secAlg_const_mul_eq_zero e (ParDVR e n v) (integralModel I) (parPrime e n v).primeCompl hQ
    (modelR e I v) hmodel (parY e n v) rfl (c ^ k) (pow_ne_zero _ hc0) b ?_
  rw [map_pow, map_pow, hq, map_mul, mul_comm (algebraMap _ _ r), mul_assoc, hrb', mul_zero]
end SecBTorsionFree
end GroundTheory.Heights₂.Heights.Vertical
