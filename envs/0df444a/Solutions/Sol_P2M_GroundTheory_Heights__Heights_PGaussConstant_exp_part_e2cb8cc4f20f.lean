-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PGaussConstant_exp_part_e2cb8cc4f20f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:45:51.880807+00:00
-- url     : https://prove2.me/submissions/b9c9f610-89d0-40e0-832b-1fa7816540b7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGauss
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PGaussConstant

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
open GroundTheory.Heights₂.Heights.PGaussConstant
namespace GroundTheory.Heights₂.Heights.PGaussConstant
theorem _root_.solution (n : ℕ) (hn : 1 ≤ n) :
    2 * (Real.exp √(n : ℝ) * Real.exp ((n : ℝ) / (2 * π))) ≤ 2 ^ n * Real.exp 2 ^ n := by
  have hx : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h2 : (2 : ℝ) ≤ 2 ^ n := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
  have hs : √(n : ℝ) ≤ n := by
    have := Real.sqrt_le_sqrt (show (n : ℝ) ≤ (n : ℝ) ^ 2 by nlinarith)
    rwa [Real.sqrt_sq (by linarith)] at this
  have hpi : (n : ℝ) / (2 * π) ≤ n := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [Real.pi_gt_three]
  have he : Real.exp √(n : ℝ) * Real.exp ((n : ℝ) / (2 * π)) ≤ Real.exp 2 ^ n := by
    rw [← Real.exp_add, ← Real.exp_nat_mul]
    exact Real.exp_le_exp.mpr (by linarith)
  exact mul_le_mul h2 he (by positivity) (by positivity)
end GroundTheory.Heights₂.Heights.PGaussConstant
