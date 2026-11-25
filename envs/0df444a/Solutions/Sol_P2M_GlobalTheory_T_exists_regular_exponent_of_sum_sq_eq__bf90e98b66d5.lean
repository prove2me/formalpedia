-- Prove2me | solution 1 for P2M_GlobalTheory_T_exists_regular_exponent_of_sum_sq_eq__bf90e98b66d5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:34:07.746163+00:00
-- url     : https://prove2.me/submissions/63036648-50e8-45b7-84df-463b598b1ab1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsRegularExponentOfSumSqEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsRegularExponentOfSumSqEqStatement
import Theorems.Thm_GlobalTheory_exists_regular_exponent_of_sum_sq_eq


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
theorem _root_.solution : ∀ (q d : ℕ) (a : ℕ → ℤ), 2 ≤ q → 0 < d → (∀ k l i : ℕ, k * q ^ i ≡ l [MOD q ^ d - 1] → a k = a l) → ∑ k ∈ Finset.range (q ^ d - 1), a k ^ 2 = d → (∀ s e l : ℕ, s * e = d → l * q ^ e ≡ l [MOD q ^ d - 1] → (s : ℤ) ∣ a l) → ∃ k : ℕ, a k ≠ 0 ∧ ∀ i : ℕ, 0 < i → i < d → ¬ k * q ^ i ≡ k [MOD q ^ d - 1] := by
  first | exact @GlobalTheory.exists_regular_exponent_of_sum_sq_eq | exact GlobalTheory.exists_regular_exponent_of_sum_sq_eq | (intros; apply GlobalTheory.exists_regular_exponent_of_sum_sq_eq <;> assumption)
end _root_.GlobalTheory.T
