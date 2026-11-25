-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_AddBlockFunctionField_pullDeg_inl_97aa8e9e178f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:52:15.473489+00:00
-- url     : https://prove2.me/submissions/f78bbf8e-1eec-4418-8e5f-751791f38ed8

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
theorem _root_.solution (b : K → ℤ) :
    pullDeg (Function.Embedding.inl : K ↪ K ⊕ L) b = IndefiniteRowSideFullHecke.FieldNumbers.pullDeg (L := L) b := by
  funext x
  cases x with
  | inl k =>
    exact (Sum.inl_injective.extend_apply b 0 k)
  | inr l =>
    refine Function.extend_apply' _ _ _ ?_
    rintro ⟨k, hk⟩
    exact Sum.inl_ne_inr hk
end GroundTheory.Heights₂.Heights.FieldNumbers.AddBlockFunctionField
