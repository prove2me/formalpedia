-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PGaussTermBound_pow_le_sqrt_pow_mul_exp_ac18c288441e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:46:07.292391+00:00
-- url     : https://prove2.me/submissions/8740fb81-2964-4f79-a763-2ded7b3f1116

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
theorem _root_.solution (n m : ℕ) (hn : 1 ≤ n) :
    ((m : ℝ) + 1) ^ n ≤ √(n : ℝ) ^ n * Real.exp (√(n : ℝ) * ((m : ℝ) + 1)) := by
  set s := √(n : ℝ) with hs_def
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < s := Real.sqrt_pos.2 hn'
  have hss : s * s = n := Real.mul_self_sqrt hn'.le
  have hm : (0 : ℝ) ≤ (m : ℝ) + 1 := by positivity
  have h1 := Real.pow_div_factorial_le_exp (s * ((m : ℝ) + 1)) (mul_nonneg hs.le hm) n
  have hfac : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  rw [div_le_iff₀ hfac] at h1
  have hfac2 : (n.factorial : ℝ) ≤ s ^ n * s ^ n := by
    rw [← mul_pow, hss]
    exact_mod_cast Nat.factorial_le_pow n
  have hE : 0 ≤ Real.exp (s * ((m : ℝ) + 1)) := (Real.exp_pos _).le
  have h2 : s ^ n * ((m : ℝ) + 1) ^ n ≤ s ^ n * (s ^ n * Real.exp (s * ((m : ℝ) + 1))) := by
    rw [← mul_pow]
    calc (s * ((m : ℝ) + 1)) ^ n ≤ Real.exp (s * ((m : ℝ) + 1)) * (n.factorial : ℝ) := h1
      _ ≤ Real.exp (s * ((m : ℝ) + 1)) * (s ^ n * s ^ n) := mul_le_mul_of_nonneg_left hfac2 hE
      _ = s ^ n * (s ^ n * Real.exp (s * ((m : ℝ) + 1))) := by ring
  exact le_of_mul_le_mul_left h2 (pow_pos hs n)
end GroundTheory.Heights₂.Heights.PGaussTermBound
