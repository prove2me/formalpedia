-- Prove2me | solution 1 for PI.SqfRootsInj.W.sq_le_four_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:26:36.092734+00:00
-- url     : https://prove2.me/submissions/b401379f-10f1-4ef1-bc26-8af89896cdb2

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_CardLeSumOfCover
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_SumSqPowLeTwo

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
theorem _root_.solution (e : ℕ) (he : 1 ≤ e) : e ^ 2 ≤ 4 ^ (e - 1) := by
  induction e with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; norm_num
    · have h1 := ih h
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      rw [Nat.add_sub_cancel] at h1
      rw [show m + 1 + 1 - 1 = m + 1 by omega, pow_succ 4 m]
      nlinarith
end PI.SqfRootsInj.W
