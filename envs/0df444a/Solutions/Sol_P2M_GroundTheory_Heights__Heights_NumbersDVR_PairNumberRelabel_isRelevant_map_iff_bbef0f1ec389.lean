-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_PairNumberRelabel_isRelevant_map_iff_bbef0f1ec389
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:14:24.918483+00:00
-- url     : https://prove2.me/submissions/87bf4e46-edaa-45a5-b247-07b2a0d6aa1a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsPairNumberRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_IntNumRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PRenameMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PRenameMultiProjPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PExistsUniqueRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPairNumberRelabel
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_PairNumberRelabel_rename_mem_map_iff_df39c23ac3ea
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_PairNumberRelabel_isRelevant_iff__96fb149ae8ef

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
variable (e : K₁ ≃ K₂)
namespace GroundTheory.Heights₂.Heights.NumbersDVR.PairNumberRelabel
theorem _root_.solution (hσ : ∀ v, (σ v).1 = e v.1) (W : Ideal (MRing ι₁ R)) :
    IsRelevant (W.map (ren (R := R) σ : MRing ι₁ R →+* MRing ι₂ R)) ↔ IsRelevant W := by
  have hX : ∀ q : Σ k, ι₂ k, (X q : MRing ι₂ R) = rename σ (X (σ.symm q)) := fun q => by
    rw [rename_X, Equiv.apply_symm_apply]
  rw [isRelevant_iff', isRelevant_iff']
  constructor
  · intro h k
    obtain ⟨q, hq, hX'⟩ := h (e k)
    refine ⟨σ.symm q, e.injective ?_, ?_⟩
    · rw [← hσ, Equiv.apply_symm_apply, hq]
    · rwa [hX, rename_mem_map_iff] at hX'
  · intro h k
    obtain ⟨p, hp, hX'⟩ := h (e.symm k)
    refine ⟨σ p, by rw [hσ, hp, Equiv.apply_symm_apply], ?_⟩
    rwa [← rename_X, rename_mem_map_iff]
end GroundTheory.Heights₂.Heights.NumbersDVR.PairNumberRelabel
