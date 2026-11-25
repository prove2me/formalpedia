-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_PairNumberRelabel_isRelevant_iff__96fb149ae8ef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:42:19.837951+00:00
-- url     : https://prove2.me/submissions/7cab14eb-e529-4329-b8f9-ee156beb27dc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsPairNumberRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_IntNumRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PRenameMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PRenameMultiProjPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PExistsUniqueRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPairNumberRelabel

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
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.PairNumberRelabel
variable {K₁ K₂ : Type} {ι₁ : K₁ → Type} {ι₂ : K₂ → Type} {R : Type} [CommRing R]
  (σ : (Σ k, ι₁ k) ≃ (Σ k, ι₂ k))
namespace GroundTheory.Heights₂.Heights.NumbersDVR.PairNumberRelabel
theorem _root_.solution {K : Type} {ι : K → Type} (W : Ideal (MRing ι R)) :
    IsRelevant W ↔ ∀ k, ∃ p : Σ k, ι k, p.1 = k ∧ (X p : MRing ι R) ∉ W := by
  refine ⟨fun h k => ?_, fun h k => ?_⟩
  · obtain ⟨i, hi⟩ := h k
    exact ⟨⟨k, i⟩, rfl, hi⟩
  · obtain ⟨⟨a, b⟩, rfl, hp⟩ := h k
    exact ⟨b, hp⟩
end GroundTheory.Heights₂.Heights.NumbersDVR.PairNumberRelabel
