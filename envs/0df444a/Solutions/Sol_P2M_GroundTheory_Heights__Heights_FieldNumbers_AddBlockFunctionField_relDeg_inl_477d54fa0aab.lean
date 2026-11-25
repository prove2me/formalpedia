-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_AddBlockFunctionField_relDeg_inl_477d54fa0aab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:27:09.113282+00:00
-- url     : https://prove2.me/submissions/1324320d-6672-48e6-afa1-940d6f2bc639

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PfContractedHypothesesExample
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_AddBlockVarEquivFst
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_AddBlockFunctionField_pulledFunField_eq_66c74016b06a

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
theorem _root_.solution [DecidableEq K] [DecidableEq L] (P' : Ideal (MRing (Sum.elim ι ι₂) F))
    [P'.IsPrime] :
    relDeg (Function.Embedding.inl : K ↪ K ⊕ L) P' = IndefiniteRowSideFullHecke.FieldNumbers.fibreDeg ι₂ P' := by
  unfold relDeg IndefiniteRowSideFullHecke.FieldNumbers.fibreDeg
  rw [pulledFunField_eq]
  rfl
end GroundTheory.Heights₂.Heights.FieldNumbers.AddBlockFunctionField
