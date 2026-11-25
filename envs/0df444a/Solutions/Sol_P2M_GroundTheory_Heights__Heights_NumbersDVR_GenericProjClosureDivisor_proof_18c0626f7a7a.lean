-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDivisor_proof_18c0626f7a7a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:34:30.813303+00:00
-- url     : https://prove2.me/submissions/4f5160b3-b9cb-4394-bf86-b0ce09469fe0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsGenericProjClosureDivisor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsTwistedDualGensExpress
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Cartier
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGenericProjClosureDivisor
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDivisor_aeval_eq_zero_of_mem_938035ac7e4d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDivisor_mem_of_homog_344f22dd36be
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDivisor_IsZPair_cross_a0643cc62b0e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDivisor_pairs_at_cb1b12ca4a24
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_IsVerticalDivisor_of_unit_off_special_da747d91115e


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.GenericProjClosureDivisor
namespace GroundTheory.Heights₂.Heights.NumbersDVR.GenericProjClosureDivisor
theorem _root_.solution (hexp : TwistedDualGensExpress.Statement) : GenericProjClosureDivisor.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N hN E _ _ B B' hB M M' a₀ a₀' φ φ' hφ hφ' Φ _ _ _ _ e t ht hZ
  have hP : (pointIdeal O (pairProjCoord y e φ φ' t)).IsPrime := hZ.multiProj.isPrime
  have hϖP : (C ϖ : MRing (bundleIdx (bundleIdx ι M) M') O) ∉ pointIdeal O (pairProjCoord y e φ φ' t) := by
    intro hm
    have h1 : ϖ ∈ (pointIdeal O (pairProjCoord y e φ φ' t)).comap
        (C : O →+* MRing (bundleIdx (bundleIdx ι M) M') O) := hm
    rw [hZ.noTorsion, Ideal.mem_bot] at h1
    exact hϖ.ne_zero h1
  have pairs := pairs_at hexp y B B' hB a₀ a₀' φ φ' hφ hφ' e t
  obtain ⟨⟨f₀, g₀, hp₀, hg₀⟩, -⟩ := pairs _ hP le_rfl hZ.multiProj.relevant hϖP
  have hf₀ : f₀ ∉ pointIdeal O (pairProjCoord y e φ φ' t) := by
    intro hm
    obtain ⟨⟨bf, bg, -, hg, -⟩, hv⟩ := hp₀
    exact hg₀ (mem_of_homog hg (by rw [← hv]; exact aeval_eq_zero_of_mem hm))
  refine ⟨f₀, g₀, IsVerticalDivisor.of_unit_off_special hp₀.1 hf₀ hg₀ ?_, hp₀.2⟩
  intro W hW hPW hWr hϖW
  obtain ⟨⟨f₁, g₁, hp₁, hg₁⟩, ⟨f₂, g₂, hp₂, hf₂⟩⟩ := pairs W hW hPW hWr hϖW
  have h12 := hPW (hp₁.cross hp₂)
  refine ⟨g₁, f₁, hg₁, fun hf₁ => ?_, ?_⟩
  · have h' : f₁ * g₂ - (f₁ * g₂ - f₂ * g₁) ∈ W := W.sub_mem (W.mul_mem_right _ hf₁) h12
    rw [sub_sub_cancel] at h'
    rcases hW.mem_or_mem h' with h | h
    · exact hf₂ h
    · exact hg₁ h
  · rw [show g₁ * f₀ - f₁ * g₀ = f₀ * g₁ - f₁ * g₀ by ring]
    exact hp₀.cross hp₁
end GroundTheory.Heights₂.Heights.NumbersDVR.GenericProjClosureDivisor
