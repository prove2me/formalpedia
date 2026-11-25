-- Prove2me | solution 1 for PI.SqfRootShift.W.pp_lte
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:34:11.755622+00:00
-- url     : https://prove2.me/submissions/0d4fa25d-3fc7-4984-a903-41899a92d92c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootShift_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootShift_SumLeProdOfTwoLe
import Theorems.Thm_PI_SqfRootShift_W_lte_two
import Theorems.Thm_PI_SqfRootShift_W_lte_odd

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
theorem _root_.solution {p g k : ℕ} (hp : p.Prime) (hg : 2 ≤ g) (h4 : 4 ∣ g - 1) (hpg : p ∣ g - 1)
    (hk : k ≠ 0) : p ^ (g ^ k - 1).factorization p ≤ k * p ^ (g - 1).factorization p := by
  have := Fact.mk hp
  have hv : padicValNat p (g ^ k - 1) = padicValNat p (g - 1) + padicValNat p k := by
    rcases hp.eq_two_or_odd' with rfl | hodd
    · exact lte_two hg h4 hk
    · exact lte_odd hodd hg hpg hk
  rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp, hv, pow_add, mul_comm k]
  exact Nat.mul_le_mul_left _ (Nat.le_of_dvd (Nat.pos_of_ne_zero hk) pow_padicValNat_dvd)
end PI.SqfRootShift.W
