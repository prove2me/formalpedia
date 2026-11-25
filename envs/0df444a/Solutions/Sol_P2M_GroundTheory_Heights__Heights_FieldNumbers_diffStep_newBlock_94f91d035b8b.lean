-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_diffStep_newBlock_94f91d035b8b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:22:26.424104+00:00
-- url     : https://prove2.me/submissions/b41dd188-a277-4bfe-81ff-cbda6b413d80

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsAddBlock
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPNProduct

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
theorem _root_.solution (A : (K → ℤ) → ℤ) (B : ℤ → ℤ) :
    diffStep (newBlockDeg : Option K → ℤ) (prodFn A B) = prodFn A (diff1 B) := by
  funext m
  have h1 : (fun k => (m - (newBlockDeg : Option K → ℤ)) (some k)) = fun k => m (some k) := by
    funext k
    simp [newBlockDeg]
  have h2 : (m - (newBlockDeg : Option K → ℤ)) none = m none - 1 := by
    simp [newBlockDeg]
  unfold diffStep prodFn diff1
  rw [h1, h2]
  ring
end GroundTheory.Heights₂.Heights.FieldNumbers
