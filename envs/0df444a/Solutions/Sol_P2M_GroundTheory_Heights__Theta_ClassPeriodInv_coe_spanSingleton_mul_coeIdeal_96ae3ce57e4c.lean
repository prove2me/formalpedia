-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_ClassPeriodInv_coe_spanSingleton_mul_coeIdeal_96ae3ce57e4c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:42:32.332929+00:00
-- url     : https://prove2.me/submissions/2beaf94f-f1df-46a7-ae16-bdb33925a6bf

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
theorem _root_.solution (c : K) (M : Ideal (𝓞 K)) :
    ((FractionalIdeal.spanSingleton (𝓞 K)⁰ c * (M : FractionalIdeal (𝓞 K)⁰ K) :
      FractionalIdeal (𝓞 K)⁰ K) : Set K) = (fun y : 𝓞 K => c * (y : K)) '' (M : Set (𝓞 K)) := by
  ext x
  simp only [SetLike.mem_coe, FractionalIdeal.mem_singleton_mul, FractionalIdeal.mem_coeIdeal,
    Set.mem_image]
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨_, ⟨y, hy, rfl⟩, rfl⟩
end GroundTheory.Heights₂.Theta.ClassPeriodInv
