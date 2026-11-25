-- Prove2me | solution 1 for PI.SqfRootsInj.W.card_LS_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:34:17.256626+00:00
-- url     : https://prove2.me/submissions/c2f4b5ff-ea1a-4aaf-885a-e79ba6877264

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_CardLeSumOfCover
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_SumSqPowLeTwo
import Theorems.Thm_PI_SqfRootsInj_W_two_pow_card_primeFactors_le


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
theorem _root_.solution (g r n : ℕ) (hn : n ≠ 0) :
    ((LS g r n).card : ℝ) ≤ Real.log n / Real.log 2 := by
  rw [le_div_iff₀ (Real.log_pos (by norm_num))]
  have h1 : 2 ^ (LS g r n).card ≤ n :=
    (Nat.pow_le_pow_right (by norm_num) (Finset.card_filter_le _ _)).trans
      (two_pow_card_primeFactors_le hn)
  have h2 : ((2 : ℝ)) ^ (LS g r n).card ≤ n := by exact_mod_cast h1
  calc ((LS g r n).card : ℝ) * Real.log 2 = Real.log ((2 : ℝ) ^ (LS g r n).card) := by
        rw [Real.log_pow]
    _ ≤ Real.log n := Real.log_le_log (by positivity) h2
end PI.SqfRootsInj.W
