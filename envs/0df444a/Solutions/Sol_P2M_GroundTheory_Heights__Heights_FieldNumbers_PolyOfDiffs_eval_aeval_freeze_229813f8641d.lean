-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_PolyOfDiffs_eval_aeval_freeze_229813f8641d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:53:05.512515+00:00
-- url     : https://prove2.me/submissions/c2cf1025-8cff-436d-8616-4a2a91f04baa

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPolyOfDiffs

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
open GroundTheory.Heights₂.Heights.FieldNumbers.PolyOfDiffs
variable {K : Type}
variable [DecidableEq K]
namespace GroundTheory.Heights₂.Heights.FieldNumbers.PolyOfDiffs
theorem _root_.solution (s : Finset K) (N x : K → ℚ) (P : MvPolynomial K ℚ) :
    eval x (aeval (freeze s N) P) = eval (fun j => if j ∈ s then x j else N j) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p r hp hr => rw [map_add, map_add, hp, hr, map_add]
  | mul_X p j hp =>
    simp only [map_mul, hp, aeval_X, eval_X, freeze]
    split_ifs <;> simp
end GroundTheory.Heights₂.Heights.FieldNumbers.PolyOfDiffs
