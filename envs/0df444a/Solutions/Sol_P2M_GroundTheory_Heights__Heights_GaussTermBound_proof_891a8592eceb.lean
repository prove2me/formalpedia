-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GaussTermBound_proof_891a8592eceb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:29:07.866825+00:00
-- url     : https://prove2.me/submissions/2700079b-d73c-4684-981b-cec9471b70c6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGauss
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PGaussTermBound
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PGaussTermBound_pow_le_sqrt_pow_mul_exp_ac18c288441e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PGaussTermBound_exponent_le_07f83f46813d

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
namespace GroundTheory.Heights₂.Heights
namespace GaussTermBound
theorem _root_.solution : GaussTermBound.Statement := by
  intro n hn m
  have h1 := PGaussTermBound.pow_le_sqrt_pow_mul_exp n m hn
  have h2 := PGaussTermBound.exponent_le n m
  have hE : 0 ≤ Real.exp (-π * (m : ℝ) ^ 2) := (Real.exp_pos _).le
  calc ((m : ℝ) + 1) ^ n * Real.exp (-π * (m : ℝ) ^ 2)
      ≤ √(n : ℝ) ^ n * Real.exp (√(n : ℝ) * ((m : ℝ) + 1)) * Real.exp (-π * (m : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right h1 hE
    _ = √(n : ℝ) ^ n * Real.exp (√(n : ℝ) * ((m : ℝ) + 1) + -π * (m : ℝ) ^ 2) := by
        rw [Real.exp_add]; ring
    _ ≤ √(n : ℝ) ^ n * Real.exp (√(n : ℝ) + n / (2 * π) + -(m : ℝ)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 h2) (by positivity)
    _ = √(n : ℝ) ^ n * Real.exp √(n : ℝ) * Real.exp (n / (2 * π)) * Real.exp (-(m : ℝ)) := by
        rw [Real.exp_add, Real.exp_add]; ring
end GaussTermBound
end GroundTheory.Heights₂.Heights
