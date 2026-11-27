-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_BoundedInjection_pos_fc12197aac5f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:57:23.027936+00:00
-- url     : https://prove2.me/submissions/1bc83ee8-63a1-44cd-87a1-68c85e7eaa15

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsLattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StandardLatticeVecIndep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ShortFamilyEquivSmallFamilyVec
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_NormFibreVecPosOfLinearIndependent
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_norm_fibreVec_pos_of_linearIndependent_9df75dd84b55
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_exists_linearIndependent_one_910a61c0c012

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open NumberField TensorProduct
noncomputable section
variable {K : Type} [Field K] [NumberField K]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
namespace BoundedInjection
theorem _root_.solution {E' E : HermitianBundle.{0} K} {A : (K →+* ℂ) → ℝ}
    (α : BoundedInjection E' E A) (h : 0 < bundleRank E') (σ : K →+* ℂ) : 0 < A σ := by
  obtain ⟨s, hs⟩ := exists_linearIndependent_one E' h
  have hs' : LinearIndependent (𝓞 K) (α.toLinearMap ∘ s) :=
    hs.map' α.toLinearMap (LinearMap.ker_eq_bot.mpr α.injective)
  have h1 := norm_fibreVec_pos_of_linearIndependent hs' σ 0
  simp only [Function.comp_apply] at h1
  have h2 := α.norm_le σ ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] s 0)
  rw [LinearMap.lTensor_tmul, fibreNorm_one_tmul, fibreNorm_one_tmul] at h2
  have h3 := norm_nonneg (fibreVec E'.metric σ (s 0))
  by_contra hA
  have hA' := not_lt.mp hA
  nlinarith
end BoundedInjection
end GroundTheory.Heights₂.Heights.HilbertSamuel
