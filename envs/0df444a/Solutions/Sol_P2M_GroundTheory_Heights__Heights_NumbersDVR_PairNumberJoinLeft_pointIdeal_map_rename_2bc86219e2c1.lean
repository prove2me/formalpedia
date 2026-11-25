-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_PairNumberJoinLeft_pointIdeal_map_rename_2bc86219e2c1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:54:39.337574+00:00
-- url     : https://prove2.me/submissions/5bc80235-3e0a-417f-82bc-1faa3919a367

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsMoreBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsTerLast
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_InhabitLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBundles
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinVertDivIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPairNumberRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinDivDiffExpansion
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinJoinPointNumbers
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PVerticalComponentFibre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFibreVarieties
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGenericDimGe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PComponentDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_OfSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ClassListMapDomainPerm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsFieldIntersectionExample
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Assembly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinPairNumJoinLeft
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_key_d10b44fcabab
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_coeff_coeffForm_479fc53ecb0b
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_SwapLoc_IsLocData_map_eq_zero_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Heights__Heights_FieldNumbers_coeff_coeffForm_479fc53ecb0b



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IFamily IsFieldIntersection IsProjVarF)
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (IsVertDiv mcIdeal joinCoord fnField assocDeg assocVar)
open GroundTheory.Heights₂.Heights.NumbersDVR.PairNumberJoinLeft
variable {K K' K₂ : Type} {ι : K → Type} {ι' : K' → Type} {ι₂ : K₂ → Type}
namespace GroundTheory.Heights₂.Heights.NumbersDVR.PairNumberJoinLeft
theorem _root_.solution {K₁ K₃ : Type} {κ₁ : K₁ → Type} {κ₃ : K₃ → Type} (R : Type) [CommRing R]
    {Ω : Type} [Field Ω] [Algebra R Ω] (e : K₁ ≃ K₃) (σ : (Σ k, κ₁ k) ≃ (Σ k, κ₃ k))
    (hσ : ∀ v, (σ v).1 = e v.1) (y : (Σ k, κ₁ k) → Ω) :
    (pointIdeal R y).map (rename σ) = pointIdeal R (y ∘ σ.symm) := by
  have hp : ∀ p, (σ.symm p).1 = e.symm p.1 := fun p => by
    rw [Equiv.eq_symm_apply, ← hσ, Equiv.apply_symm_apply]
  have key : (pointConeMap R y).comp (rename σ.symm) =
      ((rename e.symm).restrictScalars R).comp (pointConeMap R (y ∘ σ.symm)) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [pointConeMap, hp]
  have hmap : (pointIdeal R y).map (rename σ) = (pointIdeal R y).comap (rename σ.symm) := by
    have h := Ideal.map_comap_of_equiv (I := pointIdeal R y) (renameEquiv R σ).toRingEquiv
    exact h
  rw [hmap]
  ext f
  rw [Ideal.mem_comap]
  unfold pointIdeal
  rw [RingHom.mem_ker, RingHom.mem_ker]
  have hf := congrArg (fun φ => φ f) key
  simp only [AlgHom.comp_apply] at hf
  change (pointConeMap R y) (rename σ.symm f) = 0 ↔ _
  rw [hf, AlgHom.restrictScalars_apply]
  exact map_eq_zero_iff _ (rename_injective _ e.symm.injective)
end GroundTheory.Heights₂.Heights.NumbersDVR.PairNumberJoinLeft
