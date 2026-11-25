-- Prove2me | solution 1 for PI.SqfRootShift.W.ppSum_le_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:26:44.432897+00:00
-- url     : https://prove2.me/submissions/4e2a80c4-ea9f-4ee0-a6be-4c49056bd789

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootShift_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootShift_SumLeProdOfTwoLe
import Theorems.Thm_PI_SqfRootShift_W_sum_le_prod_of_two_le
import Theorems.Thm_PI_SqfRootShift_W_two_le_pp
import Theorems.Thm_PI_SqfRootShift_W_prod_pp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open PI PI.SqfRootShift PI.SqfRootShift.W
namespace PI.SqfRootShift.W
theorem _root_.solution {N : ℕ} (hN : N ≠ 0) : ppSum N ≤ N := by
  unfold ppSum
  calc _ ≤ ∏ p ∈ N.primeFactors, p ^ N.factorization p :=
        sum_le_prod_of_two_le _ _ (fun p hp => two_le_pp hp)
    _ = N := prod_pp hN
end PI.SqfRootShift.W
