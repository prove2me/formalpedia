-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GaussConstant_proof_1145429a1cab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:54:36.763621+00:00
-- url     : https://prove2.me/submissions/4dbd25d0-4320-4250-81fd-e45f5f60f6f8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGauss
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PGaussConstant
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PGaussConstant_rhs_eq_c9164907bfb1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PGaussConstant_exp_part_e2cb8cc4f20f

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
noncomputable section
open PGaussConstant
namespace GroundTheory.Heights₂.Heights
namespace GaussConstant
theorem _root_.solution : GaussConstant.Statement := by
  intro n hn
  rw [rhs_eq, gaussShellConst]
  have key := exp_part n hn
  have hc : 0 ≤ √2 ^ n * 3 ^ n * √(n : ℝ) ^ n := by positivity
  calc √2 ^ n * (2 * (3 ^ n * √(n : ℝ) ^ n * Real.exp √(n : ℝ) * Real.exp ((n : ℝ) / (2 * π))))
      = (√2 ^ n * 3 ^ n * √(n : ℝ) ^ n) *
          (2 * (Real.exp √(n : ℝ) * Real.exp ((n : ℝ) / (2 * π)))) := by ring
    _ ≤ (√2 ^ n * 3 ^ n * √(n : ℝ) ^ n) * (2 ^ n * Real.exp 2 ^ n) :=
        mul_le_mul_of_nonneg_left key hc
    _ = (6 * √2 * Real.exp 2 * √(n : ℝ)) ^ n := by
        rw [show (6 : ℝ) = 2 * 3 by norm_num]; simp only [mul_pow]; ring
end GaussConstant
end GroundTheory.Heights₂.Heights
