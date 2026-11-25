-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_ClassPeriodInv_intNorm_eq_mul_conj_7233410381a1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:51:28.262333+00:00
-- url     : https://prove2.me/submissions/c67810f2-0186-498f-8227-65e3cb3c563b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmStatements
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmEtaLogPeriodNegConjPf
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmClassPeriodInvConj
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_ClassPeriodInv_norm_eq_mul_conj_62d437d61d69

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
    (g : K ≃ₐ[ℚ] K) (hg : ∀ x, σ (g x) = starRingEnd ℂ (σ x)) (x : 𝓞 K) :
    algebraMap ℤ (𝓞 K) (Algebra.intNorm ℤ (𝓞 K) x) = x * intAut g x := by
  apply RingOfIntegers.coe_injective
  have h1 := Algebra.algebraMap_intNorm (A := ℤ) (K := ℚ) (B := 𝓞 K) (L := K) x
  have h2 := norm_eq_mul_conj hK σ hσ g hg (x : K)
  rw [← h1] at h2
  simpa using h2
end GroundTheory.Heights₂.Theta.ClassPeriodInv
