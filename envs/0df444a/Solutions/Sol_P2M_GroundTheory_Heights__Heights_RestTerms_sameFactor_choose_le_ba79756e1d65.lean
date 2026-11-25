-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_sameFactor_choose_le_ba79756e1d65
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:29:25.242872+00:00
-- url     : https://prove2.me/submissions/c539f6e2-fd74-4089-b590-0d57c66267e6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsTop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PowerSums
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSameFactorBound
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_sameFactor_descFactorial_le_5a1e7d0bb638

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
theorem _root_.solution (r a k : ℕ) (hk1 : 1 ≤ k) (hkN : k ≤ r + a) :
    (Nat.choose (r * a + k) k : ℚ) * 2 ^ (k - 1) / ((r * a : ℕ) + 1 : ℚ) ≤
      restX r a ^ (k - 1) / (k.factorial : ℚ) := by
  have h := sameFactor_descFactorial_le (r * a) (r + a) k hk1 hkN
  rw [Nat.descFactorial_eq_factorial_mul_choose] at h
  have hq : ((k.factorial * Nat.choose (r * a + k) k * 2 ^ (k - 1) : ℕ) : ℚ) ≤
      ((((r * a) + 1) * (2 * ((r * a) + (r + a))) ^ (k - 1) : ℕ) : ℚ) := by exact_mod_cast h
  have hX : restX r a = ((2 * ((r * a) + (r + a)) : ℕ) : ℚ) := by
    simp only [restX]; push_cast; ring
  rw [div_le_div_iff₀ (by positivity) (by positivity), hX]
  push_cast at hq ⊢
  linarith
end GroundTheory.Heights₂.Heights.RestTerms
