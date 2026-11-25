-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinPointFlagModel_fnField_join_e0160102ab7a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:39:41.378693+00:00
-- url     : https://prove2.me/submissions/4bfc23bf-b873-415c-a6f4-50f185507f06

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsTerTer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsBisRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsTerMore
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsTerExtra
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinJoinPointFlagModel

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
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg joinCoord restrictChart pullDeg liftVar ptIdx ptCoord chartMon
  IsGradedFrame IsUnitOn FlagPair IsPull fnField IsVertDiv mcIdeal)
open GroundTheory.Heights₂.Heights.NumbersDVR.JoinPointFlagModel
variable (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Ω : Type*} [Field Ω]
  [Algebra O Ω]
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {N : ℕ} {E : Type*} [AddCommGroup E] [Module Ω E]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.JoinPointFlagModel
theorem _root_.solution (y : (Σ k, ι k) → Ω) :
    fnField O (joinCoord y (ptCoord (Ω := Ω))) = fnField O y := by
  unfold fnField
  apply le_antisymm
  · rw [Subfield.closure_le]
    rintro a (ha | ⟨⟨k | u, i, j⟩, rfl⟩)
    · exact Subfield.subset_closure (Or.inl ha)
    · exact Subfield.subset_closure (Or.inr ⟨⟨k, i, j⟩, rfl⟩)
    · have h1 : joinCoord y (ptCoord (Ω := Ω)) ⟨Sum.inr u, i⟩ /
          joinCoord y (ptCoord (Ω := Ω)) ⟨Sum.inr u, j⟩ = 1 := by
        simp [joinCoord, ptCoord]
      simp only at h1 ⊢
      rw [h1]
      exact one_mem _
  · apply Subfield.closure_mono
    rintro a (ha | ⟨⟨k, i, j⟩, rfl⟩)
    · exact Or.inl ha
    · exact Or.inr ⟨⟨Sum.inl k, i, j⟩, rfl⟩
end GroundTheory.Heights₂.Heights.NumbersDVR.JoinPointFlagModel
