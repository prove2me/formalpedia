-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_foldr_newBlock_ce47eadd08da
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:59:06.567206+00:00
-- url     : https://prove2.me/submissions/1a48e5ce-bde8-4fc3-bf29-d6cf1c863eb9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsAddBlock
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPNProduct
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_diffStep_newBlock_94f91d035b8b

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
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR Filter
noncomputable section
universe u
variable {K : Type}
namespace GroundTheory.Heights₂.Heights.FieldNumbers
theorem _root_.solution (j : ℕ) (A : (K → ℤ) → ℤ) (B : ℤ → ℤ) :
    (List.replicate j (newBlockDeg : Option K → ℤ)).foldr diffStep (prodFn A B) =
      prodFn A (diff1^[j] B) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [List.replicate_succ, List.foldr_cons, ih, diffStep_newBlock,
      Function.iterate_succ_apply']
end GroundTheory.Heights₂.Heights.FieldNumbers
