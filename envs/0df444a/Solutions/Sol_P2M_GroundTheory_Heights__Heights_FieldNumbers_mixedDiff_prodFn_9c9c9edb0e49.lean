-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_mixedDiff_prodFn_9c9c9edb0e49
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:28:55.917251+00:00
-- url     : https://prove2.me/submissions/caf1613b-abf3-4f14-a7a4-9f256f110510

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsAddBlock
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPNProduct
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_foldr_pull_f207d38574a0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_foldr_newBlock_ce47eadd08da

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
theorem _root_.solution {m r : ℕ} (cs : Fin r → K → ℤ) (A : (K → ℤ) → ℤ) (B : ℤ → ℤ) :
    mixedDiff (Fin.append (fun _ : Fin m => (newBlockDeg : Option K → ℤ))
        (fun i => pullDeg Function.Embedding.some (cs i))) (prodFn A B) =
      prodFn (mixedDiff cs A) (diff1^[m] B) := by
  have h : List.ofFn (fun i => pullDeg Function.Embedding.some (cs i)) =
      (List.ofFn cs).map (pullDeg Function.Embedding.some) := by
    rw [List.map_ofFn]
    rfl
  unfold mixedDiff
  rw [List.ofFn_fin_append, List.foldr_append, List.ofFn_const, h, foldr_pull, foldr_newBlock]
end GroundTheory.Heights₂.Heights.FieldNumbers
