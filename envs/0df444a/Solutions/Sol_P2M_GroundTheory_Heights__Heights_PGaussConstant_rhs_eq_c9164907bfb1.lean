-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PGaussConstant_rhs_eq_c9164907bfb1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:45:52.474245+00:00
-- url     : https://prove2.me/submissions/69f9893a-a0c7-4312-9e42-03537c842e65

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
theorem _root_.solution (n : ℕ) :
    (72 * Real.exp 4 * (n : ℝ)) ^ ((n : ℝ) / 2) = (6 * √2 * Real.exp 2 * √(n : ℝ)) ^ n := by
  have hx : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have ha : 0 ≤ 6 * √2 * Real.exp 2 * √(n : ℝ) := by positivity
  have hsq : 72 * Real.exp 4 * (n : ℝ) = (6 * √2 * Real.exp 2 * √(n : ℝ)) ^ 2 := by
    have h4 : Real.exp 2 ^ 2 = Real.exp 4 := by
      rw [← Real.exp_nat_mul]; norm_num
    have : (6 * √2 * Real.exp 2 * √(n : ℝ)) ^ 2
        = 36 * (√2) ^ 2 * (Real.exp 2) ^ 2 * (√(n : ℝ)) ^ 2 := by ring
    rw [this, Real.sq_sqrt (by norm_num), Real.sq_sqrt hx, h4]
    ring
  rw [hsq, ← Real.rpow_natCast (6 * √2 * Real.exp 2 * √(n : ℝ)) 2, ← Real.rpow_mul ha,
    ← Real.rpow_natCast]
  congr 1
  push_cast
  ring
end GroundTheory.Heights₂.Heights.PGaussConstant
