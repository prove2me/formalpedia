-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_projectiveLineClassData_psi_surjective_84800f6dd64e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:44:18.432968+00:00
-- url     : https://prove2.me/submissions/0eeb6f32-6d56-4a62-bc67-69155acd5834

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_DiscrNegAndAbsNormMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_DedekindZetaSeries_SummableDedekindZetaTerm
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_DedekindZetaEqSumRealEisenstein

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
open GroundTheory.Heights₂.Theta.projectiveLineClassData
open NumberField UpperHalfPlane
open scoped nonZeroDivisors
variable {K : Type} [Field K] [NumberField K]
open FractionalIdeal EtaPeriodLatticeClass
local notation "↑ᶠ" J => ((J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)
namespace GroundTheory.Heights₂.Theta.projectiveLineClassData
theorem _root_.solution (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : Function.Surjective (psi J) := by
  rintro ⟨⟨I, hI⟩, hcl⟩
  have hcl' : ClassGroup.mk0 ⟨I, hI⟩ = (ClassGroup.mk K J)⁻¹ := hcl
  have h1 : ClassGroup.mk K (FractionalIdeal.mk0 K ⟨I, hI⟩ * J) = 1 := by
    rw [map_mul, ClassGroup.mk_mk0, hcl', inv_mul_cancel]
  rw [ClassGroup.mk_eq_one_iff] at h1
  set P := FractionalIdeal.mk0 K ⟨I, hI⟩ * J with hP
  have hPval : (P : FractionalIdeal (𝓞 K)⁰ K) = (I : FractionalIdeal (𝓞 K)⁰ K) * (↑ᶠ J) := by
    rw [hP, Units.val_mul, FractionalIdeal.coe_mk0]
  have hgen := FractionalIdeal.eq_spanSingleton_of_principal (P : FractionalIdeal (𝓞 K)⁰ K)
  set x := Submodule.IsPrincipal.generator ((P : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)
  have hxP : x ∈ (P : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [hgen]; exact mem_spanSingleton_self _ _
  have hxJ : x ∈ (↑ᶠ J) := by
    rw [hPval] at hxP
    have hle : (I : FractionalIdeal (𝓞 K)⁰ K) * (↑ᶠ J) ≤ (↑ᶠ J) := by
      calc (I : FractionalIdeal (𝓞 K)⁰ K) * (↑ᶠ J) ≤ 1 * (↑ᶠ J) := by
            rw [FractionalIdeal.mul_le]
            intro i hi j hj
            exact mul_mem_mul (coeIdeal_le_one hi) hj
        _ = (↑ᶠ J) := one_mul _
    exact hle hxP
  have hx0 : x ≠ 0 := by
    intro h0
    have : (P : FractionalIdeal (𝓞 K)⁰ K) = 0 := by rw [hgen, h0, spanSingleton_zero]
    exact Units.ne_zero P this
  refine ⟨⟨x, hxJ, hx0⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  apply coeIdeal_injective (K := K)
  change (((psi J ⟨x, hxJ, hx0⟩ : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) = _
  rw [coe_psi, ← hgen, hPval, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
end GroundTheory.Heights₂.Theta.projectiveLineClassData
