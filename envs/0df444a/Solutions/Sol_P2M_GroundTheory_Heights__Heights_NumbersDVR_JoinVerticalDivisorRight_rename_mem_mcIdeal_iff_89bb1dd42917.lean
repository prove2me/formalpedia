-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinVerticalDivisorRight_rename_mem_mcIdeal_iff_89bb1dd42917
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:25:06.997375+00:00
-- url     : https://prove2.me/submissions/77be08f8-128d-46a4-a0e8-423f078f87d5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsMoreAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisorAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinJoinVertDivRight
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinVerticalDivisorRight_mcMap_rename_midVar_8ade0d3b342f

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
open GroundTheory.Heights₂.Heights.NumbersDVR.JoinVerticalDivisorRight
variable {K K' K₂ : Type} {ι : K → Type} {ι' : K' → Type} {ι₂ : K₂ → Type}
namespace GroundTheory.Heights₂.Heights.NumbersDVR.JoinVerticalDivisorRight
theorem _root_.solution (R : Type) [CommRing R] {Ω : Type} [Field Ω] [Algebra R Ω]
    (x : (Σ k, ι k) → Ω) (w : (Σ k, ι₂ k) → Ω) (z : (Σ k, ι' k) → Ω)
    (h : MvPolynomial (Σ k : K ⊕ K', Sum.elim ι ι' k) R) :
    rename (midVar ι₂) h ∈ mcIdeal R (joinCoord x (joinCoord w z)) ↔ h ∈ mcIdeal R (joinCoord x z) := by
  simp only [mcIdeal, RingHom.mem_ker, mcMap_rename_midVar]
  exact map_eq_zero_iff _ (rename_injective _ (Sum.map_injective.mpr ⟨Function.injective_id,
    Sum.inr_injective⟩))
end GroundTheory.Heights₂.Heights.NumbersDVR.JoinVerticalDivisorRight
