-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinVerticalDivisorRight_proof_5c817b0d58ba
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:07:07.060238+00:00
-- url     : https://prove2.me/submissions/51b33d4e-2345-4bfd-ba09-d3ddd025cc6e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsMoreAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisorAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinJoinVertDivRight
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinVerticalDivisorRight_rename_mem_mcIdeal_iff_89bb1dd42917
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinVerticalDivisorRight_isMultiHomog_rename__00d542f095e1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinVerticalDivisorRight_comap_isMultiProjPrime_82eaea2a9635

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
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (IsVertDiv mcIdeal mcMap joinCoord midDeg midVar)
noncomputable section
open JoinVerticalDivisorRight
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace JoinVerticalDivisorRight
theorem _root_.solution : JoinVerticalDivisorRight.Statement := by
  intro O _ _ _ Ω _ _ K _ ι _ x K' _ ι' _ z K₂ _ ι₂ _ w b f g hD
  obtain ⟨⟨α, β, hf, hg, hb⟩, hfP, hgP, hU⟩ := hD
  refine ⟨⟨midNat α, midNat β, isMultiHomog_rename' hf, isMultiHomog_rename' hg, ?_⟩, ?_, ?_, ?_⟩
  · rintro (k | k | k)
    · exact hb (.inl k)
    · simp [midNat, midDeg]
    · exact hb (.inr k)
  · rwa [rename_mem_mcIdeal_iff]
  · rwa [rename_mem_mcIdeal_iff]
  · intro Q hQ hPQ hQO
    have hle : mcIdeal O (joinCoord x z) ≤ Q.comap (rename (midVar (ι := ι) (ι' := ι') ι₂)) :=
      fun h hh => Ideal.mem_comap.mpr (hPQ ((rename_mem_mcIdeal_iff O x w z h).mpr hh))
    have hO : (Q.comap (rename (midVar (ι := ι) (ι' := ι') ι₂))).comap
        (C : O →+* ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O (Sum.elim ι ι')) = ⊥ := by
      rw [eq_bot_iff] at hQO ⊢
      intro c hc
      apply hQO
      simpa [Ideal.mem_comap, rename_C] using hc
    obtain ⟨u, v, ⟨γ, hu⟩, ⟨δ, hv⟩, huQ, hvQ, huv⟩ := hU _ (comap_isMultiProjPrime hQ) hle hO
    refine ⟨rename (midVar ι₂) u, rename (midVar ι₂) v, ⟨_, isMultiHomog_rename' hu⟩,
      ⟨_, isMultiHomog_rename' hv⟩, huQ, hvQ, ?_⟩
    have := (rename_mem_mcIdeal_iff O x w z _).mpr huv
    simpa only [map_sub, map_mul] using this
end JoinVerticalDivisorRight
end GroundTheory.Heights₂.Heights.NumbersDVR
