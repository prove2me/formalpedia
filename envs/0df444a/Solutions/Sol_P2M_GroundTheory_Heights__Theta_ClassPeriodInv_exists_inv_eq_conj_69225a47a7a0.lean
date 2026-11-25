-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_ClassPeriodInv_exists_inv_eq_conj_69225a47a7a0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:32:37.76261+00:00
-- url     : https://prove2.me/submissions/c05110bb-2e8b-418d-aff4-5bd309aace7a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmStatements
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmEtaLogPeriodNegConjPf
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmClassPeriodInvConj
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_ClassPeriodInv_exists_conj_aut_b79dc8972092
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_ClassPeriodInv_mul_map_eq_span_absNorm_19aa514c4350
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_ClassPeriodInv_coe_spanSingleton_mul_coeIdeal_96ae3ce57e4c

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
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ∃ w : ℂ, w ≠ 0 ∧ σ '' (((I⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) :
      Set K) = (fun z => w * z) '' (starRingEnd ℂ '' (σ '' ((I : FractionalIdeal (𝓞 K)⁰ K) :
        Set K))) := by
  obtain ⟨g, hg⟩ := exists_conj_aut hK σ
  obtain ⟨a, I₀, ha, hI⟩ := FractionalIdeal.exists_eq_spanSingleton_mul (I : FractionalIdeal (𝓞 K)⁰ K)
  have hI₀ : I₀ ≠ ⊥ := by
    rintro rfl
    apply I.ne_zero
    rw [hI]
    simp
  set n : 𝓞 K := ((Ideal.absNorm I₀ : ℤ) : 𝓞 K) with hn
  have hn0 : algebraMap (𝓞 K) K n ≠ 0 := by
    have : (Ideal.absNorm I₀ : ℤ) ≠ 0 := by
      exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr hI₀)
    simpa [hn] using this
  have ha0 : algebraMap (𝓞 K) K a ≠ 0 := by
    simpa using ha
  set A : K := algebraMap (𝓞 K) K a with hA
  set N : K := algebraMap (𝓞 K) K n with hN
  set J : FractionalIdeal (𝓞 K)⁰ K := FractionalIdeal.spanSingleton (𝓞 K)⁰ (A / N) *
    ((I₀.map (intAut g) : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) with hJdef
  have hIJ : (I : FractionalIdeal (𝓞 K)⁰ K) * J = 1 := by
    rw [hI, hJdef]
    calc _ = FractionalIdeal.spanSingleton (𝓞 K)⁰ (A⁻¹ * (A / N)) *
          ((I₀ * I₀.map (intAut g) : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by
          rw [FractionalIdeal.coeIdeal_mul, ← FractionalIdeal.spanSingleton_mul_spanSingleton]
          ring
      _ = 1 := by
          rw [mul_map_eq_span_absNorm hK σ hσ g hg, FractionalIdeal.coeIdeal_span_singleton,
            ← hn, FractionalIdeal.spanSingleton_mul_spanSingleton, ← hN,
            show A⁻¹ * (A / N) * N = 1 by field_simp]
          exact FractionalIdeal.spanSingleton_one
  have hJ : ((I⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) = J :=
    Units.inv_eq_of_mul_eq_one_right hIJ
  refine ⟨σ (A / N) * starRingEnd ℂ (σ A), ?_, ?_⟩
  · refine mul_ne_zero ?_ ?_
    · exact (map_ne_zero σ).mpr (div_ne_zero ha0 hn0)
    · exact (map_ne_zero _).mpr ((map_ne_zero σ).mpr ha0)
  rw [hJ, hJdef, coe_spanSingleton_mul_coeIdeal, hI, coe_spanSingleton_mul_coeIdeal]
  have hmap : ((I₀.map (intAut g) : Ideal (𝓞 K)) : Set (𝓞 K)) = intAut g '' (I₀ : Set (𝓞 K)) := by
    ext y
    rw [SetLike.mem_coe, Ideal.mem_map_of_equiv]
    rfl
  rw [hmap]
  simp only [Set.image_image]
  refine Set.image_congr fun y _ => ?_
  have hy : ((intAut g y : 𝓞 K) : K) = g (y : K) := rfl
  rw [hy, map_mul, hg]
  simp only [map_mul, map_inv₀]
  have hσA : starRingEnd ℂ (σ A) ≠ 0 := (map_ne_zero _).mpr ((map_ne_zero σ).mpr ha0)
  field_simp
end GroundTheory.Heights₂.Theta.ClassPeriodInv
