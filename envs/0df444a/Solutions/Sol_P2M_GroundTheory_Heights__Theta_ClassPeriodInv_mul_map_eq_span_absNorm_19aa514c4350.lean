-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_ClassPeriodInv_mul_map_eq_span_absNorm_19aa514c4350
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:19:28.955457+00:00
-- url     : https://prove2.me/submissions/7c303085-6026-47ab-8205-dcc874f9fc0b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmStatements
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmEtaLogPeriodNegConjPf
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmClassPeriodInvConj
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_ClassPeriodInv_intNorm_eq_mul_conj_7233410381a1
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_ClassPeriodInv_eq_of_le_of_absNorm_eq_88c19db2ed55

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open UpperHalfPlane ModularGroup ModularForm Complex NumberField Module
open scoped Real Modular MatrixGroups nonZeroDivisors
open GroundTheory.Heights₂.Theta.ClassPeriodInv
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Heights₂.Theta.ClassPeriodInv
theorem _root_.solution (hK : finrank ℚ K = 2) (σ : K →+* ℂ) (hσ : ∃ x : K, (σ x).im ≠ 0)
    (g : K ≃ₐ[ℚ] K) (hg : ∀ x, σ (g x) = starRingEnd ℂ (σ x)) (I : Ideal (𝓞 K)) :
    I * I.map (intAut g) = Ideal.span {((Ideal.absNorm I : ℤ) : 𝓞 K)} := by
  have hspan : (Ideal.relNorm ℤ I).map (algebraMap ℤ (𝓞 K)) =
      Ideal.span {((Ideal.absNorm I : ℤ) : 𝓞 K)} := by
    rw [Ideal.relNorm_int, Ideal.map_span, Set.image_singleton]
    simp
  have hle : (Ideal.relNorm ℤ I).map (algebraMap ℤ (𝓞 K)) ≤ I * I.map (intAut g) := by
    have hdef : Ideal.relNorm ℤ I = Ideal.span (Algebra.intNorm ℤ (𝓞 K) '' I) := rfl
    rw [hdef, Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    rw [SetLike.mem_coe, intNorm_eq_mul_conj hK σ hσ g hg y]
    exact Ideal.mul_mem_mul hy (Ideal.mem_map_of_mem _ hy)
  rw [hspan] at hle
  by_cases hI : I = ⊥
  · subst hI
    simp
  have h0 : Ideal.absNorm I ≠ 0 := by
    rwa [Ne, Ideal.absNorm_eq_zero_iff]
  refine (eq_of_le_of_absNorm_eq hle ?_ ?_).symm
  · rw [← hspan, Ideal.absNorm_algebraMap, Ideal.absNorm_relNorm, map_mul,
      ← Ideal.absNorm_relNorm (R := ℤ) (I := I.map (intAut g)), Ideal.relNorm_map_algEquiv,
      Ideal.absNorm_relNorm, RingOfIntegers.rank, hK, sq]
  · rw [map_mul, ← Ideal.absNorm_relNorm (R := ℤ) (I := I.map (intAut g)), Ideal.relNorm_map_algEquiv,
      Ideal.absNorm_relNorm]
    exact mul_ne_zero h0 h0
end GroundTheory.Heights₂.Theta.ClassPeriodInv
