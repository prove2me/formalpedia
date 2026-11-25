-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_sameFactor_descFactorial_le_5a1e7d0bb638
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:13:29.026264+00:00
-- url     : https://prove2.me/submissions/92647076-48e4-411e-a2fa-3861d26d90c2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsTop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PowerSums
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSameFactorBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms
theorem _root_.solution (n₁ N : ℕ) :
    ∀ k : ℕ, 1 ≤ k → k ≤ N →
      (n₁ + k).descFactorial k * 2 ^ (k - 1) ≤ (n₁ + 1) * (2 * (n₁ + N)) ^ (k - 1)
  | 0, h, _ => absurd h (by norm_num)
  | 1, _, _ => by simp [Nat.descFactorial]
  | k + 2, _, hN => by
    have ih : (n₁ + (k + 1)).descFactorial (k + 1) * 2 ^ k ≤ (n₁ + 1) * (2 * (n₁ + N)) ^ k := by
      simpa using solution n₁ N (k + 1) (by omega) (by omega)
    have hd : (n₁ + (k + 2)).descFactorial (k + 2) =
        (n₁ + (k + 1) + 1) * (n₁ + (k + 1)).descFactorial (k + 1) := by
      rw [show n₁ + (k + 2) = n₁ + (k + 1) + 1 by omega, Nat.succ_descFactorial_succ]
    rw [show k + 2 - 1 = k + 1 by omega, pow_succ, pow_succ, hd]
    calc (n₁ + (k + 1) + 1) * (n₁ + (k + 1)).descFactorial (k + 1) * (2 ^ k * 2)
        = ((n₁ + (k + 1)).descFactorial (k + 1) * 2 ^ k) * (2 * (n₁ + (k + 1) + 1)) := by ring
      _ ≤ ((n₁ + 1) * (2 * (n₁ + N)) ^ k) * (2 * (n₁ + N)) :=
          Nat.mul_le_mul ih (by omega)
      _ = (n₁ + 1) * ((2 * (n₁ + N)) ^ k * (2 * (n₁ + N))) := by ring
end GroundTheory.Heights₂.Heights.RestTerms
