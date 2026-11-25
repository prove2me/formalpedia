-- Prove2me | solution 1 for P2M_GlobalTheory_T_exists_coprime_orderOf_pow_prime_pow__cf23029f3352
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:34:20.001862+00:00
-- url     : https://prove2.me/submissions/46e321ae-c05b-4868-9bc5-a6d951ad1f72

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsCoprimeOrderOfPowPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsCoprimeOrderOfPowPrimePowStatement
import Theorems.Thm_GlobalTheory_exists_coprime_orderOf_pow_prime_pow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (G : Type) [Group G] [Finite G] (x : G) (p : ℕ), p.Prime → ∃ k : ℕ, Nat.Coprime (orderOf (x ^ p ^ k)) p := by
  first | exact @GlobalTheory.exists_coprime_orderOf_pow_prime_pow | exact GlobalTheory.exists_coprime_orderOf_pow_prime_pow | (intros; apply GlobalTheory.exists_coprime_orderOf_pow_prime_pow <;> assumption)
end _root_.GlobalTheory.T
