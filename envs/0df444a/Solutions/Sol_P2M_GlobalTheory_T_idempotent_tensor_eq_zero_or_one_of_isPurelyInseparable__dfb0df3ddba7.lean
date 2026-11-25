-- Prove2me | solution 1 for P2M_GlobalTheory_T_idempotent_tensor_eq_zero_or_one_of_isPurelyInseparable__dfb0df3ddba7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:34:40.235671+00:00
-- url     : https://prove2.me/submissions/8dc2b706-e8e5-4ecf-b912-dd056b93b577

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IdempotentTensorEqZeroOrOneOfIsPurelyInseparable
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IdempotentTensorEqZeroOrOneOfIsPurelyInseparableStatement
import Theorems.Thm_GlobalTheory_idempotent_tensor_eq_zero_or_one_of_isPurelyInseparable


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open scoped TensorProduct
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k K B : Type) [Field k] [Field K] [Algebra k K] [IsPurelyInseparable k K] [CommRing B] [IsLocalRing B] [Algebra k B] (e : K ⊗[k] B), IsIdempotentElem e → e = 0 ∨ e = 1 := by
  first | exact @GlobalTheory.idempotent_tensor_eq_zero_or_one_of_isPurelyInseparable | exact GlobalTheory.idempotent_tensor_eq_zero_or_one_of_isPurelyInseparable | (intros; apply GlobalTheory.idempotent_tensor_eq_zero_or_one_of_isPurelyInseparable <;> assumption)
end _root_.GlobalTheory.T
