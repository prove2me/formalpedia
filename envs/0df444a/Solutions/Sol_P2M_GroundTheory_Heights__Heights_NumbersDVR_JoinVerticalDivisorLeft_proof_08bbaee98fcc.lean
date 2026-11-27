-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinVerticalDivisorLeft_proof_08bbaee98fcc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:12:50.757685+00:00
-- url     : https://prove2.me/submissions/fff33b3b-b188-4b43-84ca-a77195c20143

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsTerLast
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisorAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinJoinVertDivLeft
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinVerticalDivisorLeft_rename_assocVar_mem_mcIdeal_iff_1e71880a676b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinVerticalDivisorLeft_isMultiHomog_rename_assocVar_4a988f335c8a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinVerticalDivisorLeft_comap_isMultiProjPrime_8c49cb8f3974
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_Bundles_joinCoord_assocVar_b75e0e1aca5e


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
open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (joinCoord mcIdeal mcMap assocDeg assocVar joinCoord_assocVar IsVertDiv)
noncomputable section
open JoinVerticalDivisorLeft
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace JoinVerticalDivisorLeft
theorem _root_.solution : JoinVerticalDivisorLeft.Statement := by
  intro O _ _ _ Ω _ _ K _ ι _ x K' _ ι' _ z K₂ _ ι₂ _ w b f g hD
  obtain ⟨⟨α, β, hf, hg, hb⟩, hfP, hgP, hU⟩ := hD
  refine ⟨⟨_, _, isMultiHomog_rename_assocVar (ι₂ := ι₂) hf, isMultiHomog_rename_assocVar (ι₂ := ι₂) hg, ?_⟩,
    ?_, ?_, ?_⟩
  · rintro (k | k | k)
    · simpa [assocDeg] using hb (.inl k)
    · simpa [assocDeg] using hb (.inr k)
    · simp [assocDeg]
  · rwa [rename_assocVar_mem_mcIdeal_iff]
  · rwa [rename_assocVar_mem_mcIdeal_iff]
  · intro Q hQ hPQ hQO
    have hle : mcIdeal O (joinCoord x z) ≤ Q.comap (rename (assocVar (ι := ι) (ι' := ι') ι₂)) :=
      fun h hh => Ideal.mem_comap.mpr (hPQ ((rename_assocVar_mem_mcIdeal_iff O x z w h).mpr hh))
    have hO : (Q.comap (rename (assocVar (ι := ι) (ι' := ι') ι₂))).comap
        (C : O →+* ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O (Sum.elim ι ι')) = ⊥ := by
      rw [eq_bot_iff] at hQO ⊢
      intro c hc
      apply hQO
      simpa [Ideal.mem_comap, rename_C] using hc
    obtain ⟨u, v, ⟨γ, hu⟩, ⟨δ, hv⟩, huQ, hvQ, huv⟩ := hU _ (comap_isMultiProjPrime hQ) hle hO
    refine ⟨rename (assocVar ι₂) u, rename (assocVar ι₂) v, ⟨_, isMultiHomog_rename_assocVar hu⟩,
      ⟨_, isMultiHomog_rename_assocVar hv⟩, huQ, hvQ, ?_⟩
    have := (rename_assocVar_mem_mcIdeal_iff O x z w _).mpr huv
    simpa only [map_sub, map_mul] using this
end JoinVerticalDivisorLeft
end GroundTheory.Heights₂.Heights.NumbersDVR
