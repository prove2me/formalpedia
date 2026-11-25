-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_ClassPeriodInv_exists_eq_mul_of_mk_eq_4ce545dc440e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:42:49.863555+00:00
-- url     : https://prove2.me/submissions/fbf8fa4e-904f-4962-821f-a1dbf69a92e3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmStatements
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmEtaLogPeriodNegConjPf
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmClassPeriodInvConj

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
theorem _root_.solution {J J' : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (h : ClassGroup.mk K J' = ClassGroup.mk K J) :
    ∃ x : K, x ≠ 0 ∧ ((J' : FractionalIdeal (𝓞 K)⁰ K) : Set K) =
      (fun y => x * y) '' ((J : FractionalIdeal (𝓞 K)⁰ K) : Set K) := by
  have h1 : ClassGroup.mk K (J' * J⁻¹) = 1 := by
    rw [map_mul, map_inv, h, mul_inv_cancel]
  obtain ⟨⟨x, hx⟩⟩ := ClassGroup.mk_eq_one_iff.mp h1
  have hP : ((J' * J⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ x := by
    apply FractionalIdeal.coeToSubmodule_injective
    dsimp only
    rw [FractionalIdeal.coe_spanSingleton]
    exact hx
  have hJ' : (J' : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ x * (J : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [← hP, Units.val_mul, mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]
  have hx0 : x ≠ 0 := by
    rintro rfl
    apply J'.ne_zero
    rw [hJ', FractionalIdeal.spanSingleton_zero, zero_mul]
  refine ⟨x, hx0, ?_⟩
  ext y
  rw [hJ', SetLike.mem_coe, FractionalIdeal.mem_singleton_mul, Set.mem_image]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz, rfl⟩
end GroundTheory.Heights₂.Theta.ClassPeriodInv
