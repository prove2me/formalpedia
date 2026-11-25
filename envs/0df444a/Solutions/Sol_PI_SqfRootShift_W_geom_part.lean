-- Prove2me | solution 1 for PI.SqfRootShift.W.geom_part
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:26:21.197835+00:00
-- url     : https://prove2.me/submissions/0f9e4f8b-c22e-4bef-b9a0-f92ad96d713a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootShift_SumLeProdOfTwoLe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootShift_ArithP

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
theorem _root_.solution (G : ℝ) (r : ℕ) (hr : 1 ≤ r) :
    ∑ k ∈ Finset.Ioc 1 r, (G - 1) * G ^ (r - k) = G ^ (r - 1) - 1 := by
  induction r, hr using Nat.le_induction with
  | base => simp
  | succ r hr ih =>
    rw [Finset.sum_Ioc_succ_top (by omega : 1 ≤ r), Nat.sub_self, pow_zero, mul_one]
    have h : ∑ k ∈ Finset.Ioc 1 r, (G - 1) * G ^ (r + 1 - k) =
        G * ∑ k ∈ Finset.Ioc 1 r, (G - 1) * G ^ (r - k) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_Ioc] at hk
      rw [show r + 1 - k = (r - k) + 1 by omega, pow_succ]; ring
    rw [h, ih, show r + 1 - 1 = (r - 1) + 1 by omega, pow_succ]; ring
end PI.SqfRootShift.W
