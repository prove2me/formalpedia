-- Prove2me | solution 1 for P2M_GlobalTheory_card_zmod_tensor_eq_card_quot__bf8f7723fa84
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:34:38.266581+00:00
-- url     : https://prove2.me/submissions/9c3b49e7-d28e-4b22-a154-01b0d482e60c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardZmodTensorEqCardQuotPrimeMultiples
import Theorems.Thm_GlobalTheory_card_zmod_tensor_eq_card_quot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (M : Type) [AddCommGroup M] [Module ℤ M] (p : ℕ),
    Nat.card (TensorProduct ℤ (ZMod p) M) =
      Nat.card (M ⧸ LinearMap.range ((p : ℤ) • (LinearMap.id : M →ₗ[ℤ] M))) :=
  fun M _ _ p => card_zmod_tensor_eq_card_quot M p
end GlobalTheory
