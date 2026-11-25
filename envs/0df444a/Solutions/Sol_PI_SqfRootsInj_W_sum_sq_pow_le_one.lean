-- Prove2me | solution 1 for PI.SqfRootsInj.W.sum_sq_pow_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:40:01.257326+00:00
-- url     : https://prove2.me/submissions/f1001a65-5ff4-42a9-b0fe-276625479aa8

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_CardLeSumOfCover
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_SumSqPowLeTwo
import Theorems.Thm_PI_SqfRootsInj_W_geom_half_le
import Theorems.Thm_PI_SqfRootsInj_W_sq_mul_pow_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open Classical
open PI PI.SqfRootsInj PI.SqfRootsInj.W
open PI.SqfLab
namespace PI.SqfRootsInj.W
theorem _root_.solution (t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ 1 / 8) (n : ℕ) :
    ∑ e ∈ Finset.Icc 1 n, (e : ℝ) ^ 2 * t ^ e ≤ 2 * t := by
  calc ∑ e ∈ Finset.Icc 1 n, (e : ℝ) ^ 2 * t ^ e
      ≤ ∑ e ∈ Finset.Icc 1 n, t * (1 / 2 : ℝ) ^ (e - 1) := by
        refine Finset.sum_le_sum fun e he => ?_
        refine (sq_mul_pow_le t ht0 e (Finset.mem_Icc.1 he).1).trans ?_
        gcongr
        linarith
    _ = t * ∑ e ∈ Finset.Icc 1 n, (1 / 2 : ℝ) ^ (e - 1) := by rw [Finset.mul_sum]
    _ ≤ t * 2 := by gcongr; exact geom_half_le 1 n
    _ = 2 * t := by ring
end PI.SqfRootsInj.W
