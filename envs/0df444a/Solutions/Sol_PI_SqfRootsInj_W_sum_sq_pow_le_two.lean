-- Prove2me | solution 1 for PI.SqfRootsInj.W.sum_sq_pow_le_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:40:04.392827+00:00
-- url     : https://prove2.me/submissions/ff39f500-476e-4362-a3e8-30503d1d9a1f

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
    ∑ e ∈ Finset.Icc 2 n, (e : ℝ) ^ 2 * t ^ e ≤ 8 * t ^ 2 := by
  calc ∑ e ∈ Finset.Icc 2 n, (e : ℝ) ^ 2 * t ^ e
      ≤ ∑ e ∈ Finset.Icc 2 n, 4 * t ^ 2 * (1 / 2 : ℝ) ^ (e - 2) := by
        refine Finset.sum_le_sum fun e he => ?_
        have he2 := (Finset.mem_Icc.1 he).1
        refine (sq_mul_pow_le t ht0 e (by omega)).trans ?_
        obtain ⟨k, rfl⟩ : ∃ k, e = k + 2 := ⟨e - 2, by omega⟩
        rw [show k + 2 - 1 = k + 1 by omega, Nat.add_sub_cancel, pow_succ]
        have : (4 * t) ^ k ≤ (1 / 2 : ℝ) ^ k := pow_le_pow_left₀ (by positivity) (by linarith) k
        nlinarith [pow_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) ht0) k]
    _ = 4 * t ^ 2 * ∑ e ∈ Finset.Icc 2 n, (1 / 2 : ℝ) ^ (e - 2) := by rw [Finset.mul_sum]
    _ ≤ 4 * t ^ 2 * 2 := by gcongr; exact geom_half_le 2 n
    _ = 8 * t ^ 2 := by ring
end PI.SqfRootsInj.W
