-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_genericSubstitution_isWeightedHomogeneous_61102d448a34
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:28:04.296795+00:00
-- url     : https://prove2.me/submissions/3b6e2238-9a4f-42ee-9c6d-f86cb0dc49f1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StProjBundleMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PProjBundleMultiHomogSpan
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PProjBundleMultiHomog
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isWeightedHomogeneous_aeval_of_weights_ef9f52113e2f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_weight_comp_addMonoidHom_5b25825b175f


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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable (ι) {S : Type} [Fintype S] (γ : S → K → ℕ)
variable {ι} {N1 : ℕ}
omit [Fintype K] [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
theorem _root_.solution (V : S → Fin N1 → MRing ι)
    (hV : ∀ s j, IsWeightedHomogeneous (NumbersDVR.blockWeight ι) (V s j) (γ s))
    (v : Σ x, PBlk ι N1 x) :
    IsWeightedHomogeneous (genericWeight ι γ) (genericSubstitution V v) (zDeg (NumbersDVR.blockWeight (PBlk ι N1) v)) := by
  rcases v with ⟨k | u, i⟩
  · convert isWeightedHomogeneous_X ℤ (genericWeight ι γ) (Sum.inr ⟨k, i⟩) using 1
    · rfl
    · funext x
      cases x <;> simp [genericWeight, zDegInl, zDeg, NumbersDVR.blockWeight, Pi.single_apply]
  · have hdeg : zDeg (NumbersDVR.blockWeight (PBlk ι N1) ⟨Sum.inr u, i⟩) = Pi.single (Sum.inr ()) 1 := by
      funext x
      cases x <;> simp [zDeg, NumbersDVR.blockWeight]
    rw [hdeg]
    change Fin N1 at i
    refine IsWeightedHomogeneous.sum _ _ _ fun s _ => ?_
    have hren : IsWeightedHomogeneous (genericWeight ι γ) (rename Sum.inr (V s i) : MvPolynomial (S ⊕ _) ℤ)
        (zDegInl (γ s)) := by
      rw [rename_eq_aeval]
      refine isWeightedHomogeneous_aeval_of_weights (w := fun p => zDegInl (NumbersDVR.blockWeight ι p))
        (e := X ∘ Sum.inr)
        (fun p => isWeightedHomogeneous_X ℤ (genericWeight ι γ) (Sum.inr p)) ?_
      intro d hd
      rw [NumbersDVR.weight_comp_addMonoidHom, hV s i hd]
    convert hren.mul (isWeightedHomogeneous_X ℤ (genericWeight ι γ) (Sum.inl s)) using 1
    show _ = zDegInl (γ s) + (Pi.single (Sum.inr ()) 1 - zDegInl (γ s))
    abel
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
