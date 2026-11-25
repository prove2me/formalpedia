-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_AddBlockFunctionField_pulledFunField_eq_66c74016b06a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:52:39.621346+00:00
-- url     : https://prove2.me/submissions/4115cedc-1c3b-435c-a1e0-869074be5724

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PfContractedHypothesesExample
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_AddBlockVarEquivFst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.FieldNumbers.AddBlockFunctionField
variable {F : Type u} [Field F] {K L : Type} {ι : K → Type} {ι₂ : L → Type}
namespace GroundTheory.Heights₂.Heights.FieldNumbers.AddBlockFunctionField
theorem _root_.solution [DecidableEq K] (P' : Ideal (MRing (Sum.elim ι ι₂) F)) [P'.IsPrime] :
    IndefiniteRowSideFullHecke.FieldNumbers.pulledFunField ι₂ P' =
      (homFracDegZero (contractPrime (Function.Embedding.inl : K ↪ K ⊕ L) P')).map
        (contractFracMap Function.Embedding.inl P') := by
  unfold IndefiniteRowSideFullHecke.FieldNumbers.pulledFunField homFracDegZero
  rw [IntermediateField.adjoin_map]
  congr 1
  ext x
  constructor
  · rintro ⟨d, f, g, hf, hg, hgP, rfl⟩
    refine ⟨_, ⟨d, f, g, hf, hg, hgP, rfl⟩, ?_⟩
    simp [contractFracMap, contractQuot, map_div₀, IndefiniteRowSideFullHecke.FieldNumbers.blockIncl]
    rfl
  · rintro ⟨y, ⟨d, f, g, hf, hg, hgP, rfl⟩, rfl⟩
    refine ⟨d, f, g, hf, hg, hgP, ?_⟩
    simp [contractFracMap, contractQuot, map_div₀, IndefiniteRowSideFullHecke.FieldNumbers.blockIncl]
    rfl
end GroundTheory.Heights₂.Heights.FieldNumbers.AddBlockFunctionField
