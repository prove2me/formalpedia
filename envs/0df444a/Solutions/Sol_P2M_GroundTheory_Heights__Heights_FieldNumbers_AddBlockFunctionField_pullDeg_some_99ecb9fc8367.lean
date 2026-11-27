-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_AddBlockFunctionField_pullDeg_some_99ecb9fc8367
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:55:59.50738+00:00
-- url     : https://prove2.me/submissions/658a3efb-6c2c-47ea-b447-abc8b6b76fb0

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
variable {F : Type u} [Field F] {K : Type} {ι : K → Type}
namespace GroundTheory.Heights₂.Heights.FieldNumbers.AddBlockFunctionField
theorem _root_.solution (c : K → ℤ) :
    pullDeg (Function.Embedding.some : K ↪ Option K) c =
      IndefiniteRowSideFullHecke.FieldNumbers.pullDeg (L := Unit) c ∘ blockEquiv K := by
  funext o
  cases o with
  | some k => exact (Option.some_injective K).extend_apply c 0 k
  | none =>
    refine Function.extend_apply' _ _ _ ?_
    rintro ⟨k, hk⟩
    exact Option.some_ne_none k hk
end GroundTheory.Heights₂.Heights.FieldNumbers.AddBlockFunctionField
