-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_ClassPeriodInv_isLatticeParam_of_mem_classReducedParams_e8b7265c478f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:51:36.020885+00:00
-- url     : https://prove2.me/submissions/89eac193-06fa-43c9-bcab-3fa5b79bf8ad

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmStatements
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmEtaLogPeriodNegConjPf
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmClassPeriodInvConj
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_ClassPeriodInv_exists_eq_mul_of_mk_eq_4ce545dc440e
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_ClassPeriodInv_isLatticeParam_mul_5bec8bc1e470

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
theorem _root_.solution (σ : K →+* ℂ) {A : ClassGroup (𝓞 K)} {τ : ℍ}
    (hτ : τ ∈ classReducedParams σ A) {J : (FractionalIdeal (𝓞 K)⁰ K)ˣ} (hJ : ClassGroup.mk K J = A) :
    IsLatticeParam (σ '' ((J : FractionalIdeal (𝓞 K)⁰ K) : Set K)) τ := by
  obtain ⟨J', hJ'A, -, hpar⟩ := hτ
  obtain ⟨x, hx, hset⟩ := exists_eq_mul_of_mk_eq (hJ'A.trans hJ.symm)
  have hx' : σ x⁻¹ ≠ 0 := (map_ne_zero σ).mpr (inv_ne_zero hx)
  have hJset : σ '' ((J : FractionalIdeal (𝓞 K)⁰ K) : Set K) =
      (fun z => σ x⁻¹ * z) '' (σ '' ((J' : FractionalIdeal (𝓞 K)⁰ K) : Set K)) := by
    rw [hset]
    simp only [Set.image_image]
    refine Set.image_congr fun y _ => ?_
    rw [← map_mul, ← mul_assoc, inv_mul_cancel₀ hx, one_mul]
  rw [hJset]
  exact isLatticeParam_mul hpar hx'
end GroundTheory.Heights₂.Theta.ClassPeriodInv
