-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_foldr_pull_f207d38574a0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:13:23.382804+00:00
-- url     : https://prove2.me/submissions/655e0cb7-e2fc-4d84-a415-1278dcbc3641

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsAddBlock
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPNProduct
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_diffStep_pull_060fb2384a2d

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
theorem _root_.solution (L : List (K → ℤ)) (A : (K → ℤ) → ℤ) (B : ℤ → ℤ) :
    (L.map (pullDeg Function.Embedding.some)).foldr diffStep (prodFn A B) =
      prodFn (L.foldr diffStep A) B := by
  induction L with
  | nil => rfl
  | cons c L ih => simp only [List.map_cons, List.foldr_cons, ih, diffStep_pull]
end GroundTheory.Heights₂.Heights.FieldNumbers
