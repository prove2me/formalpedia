-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PGaussTermBound_exponent_le_07f83f46813d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:46:05.243793+00:00
-- url     : https://prove2.me/submissions/bc9b214f-fc84-4128-b822-c7daedb31e11

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGauss
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PGaussTermBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Real
open GroundTheory.Heights₂.Heights.PGaussTermBound
namespace GroundTheory.Heights₂.Heights.PGaussTermBound
theorem _root_.solution (n m : ℕ) :
    √(n : ℝ) * ((m : ℝ) + 1) + -π * (m : ℝ) ^ 2 ≤ √(n : ℝ) + n / (2 * π) + -(m : ℝ) := by
  set s := √(n : ℝ) with hs_def
  have hss : s * s = n := Real.mul_self_sqrt (Nat.cast_nonneg n)
  have hpi : 0 < π := Real.pi_pos
  have hpi3 : 3 < π := Real.pi_gt_three

  have hA : s * m - π / 2 * (m : ℝ) ^ 2 ≤ n / (2 * π) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (π * m - s)]

  have hB : (m : ℝ) ≤ π / 2 * (m : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp
    · have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast h
      nlinarith
  nlinarith
end GroundTheory.Heights₂.Heights.PGaussTermBound
