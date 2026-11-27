-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureModel_proof_bbc9ab4571d0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:06:23.772465+00:00
-- url     : https://prove2.me/submissions/bb92658b-2790-48c0-a6a6-5be4a5c56217

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsSegreClosureModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsTwistedDualGensExist
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsGenericProjClosureDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsGenericProjClosureDivisor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGenericProjClosureModel

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
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace GenericProjClosureModel
theorem _root_.solution (h₁ : TwistedDualGensExist.Statement)
    (h₂ : GenericProjClosureDim.Statement) (h₃ : GenericProjClosureDivisor.Statement) :
    GenericProjClosureModel.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N hN E _ _ B B' hB Φ _ _ _ _ e t ht
  obtain ⟨a₁, ha₁⟩ := h₁ O Ω K ι y N E B
  obtain ⟨M, φ, hφ⟩ := ha₁ a₁ le_rfl
  obtain ⟨a₁', ha₁'⟩ := h₁ O Ω K ι y N E B'
  obtain ⟨M', φ', hφ'⟩ := ha₁' a₁' le_rfl
  have hZ := h₂ O ϖ hϖ Ω K ι y d hV N hN E B B' hB M M' a₁ a₁' φ φ' hφ hφ' Φ e t ht
  obtain ⟨f₀, g₀, hD, hfg⟩ :=
    h₃ O ϖ hϖ Ω K ι y d hV N hN E B B' hB M M' a₁ a₁' φ φ' hφ hφ' Φ e t ht hZ
  exact ⟨M, M', a₁, a₁', φ, φ', hφ, hφ', hZ, f₀, g₀, hD, hfg⟩
end GenericProjClosureModel
end GroundTheory.Heights₂.Heights.NumbersDVR
