-- Prove2me | solution 1 for PI.FinOrdRedOne.Core.one_add_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:40:07.861216+00:00
-- url     : https://prove2.me/submissions/1f7a9515-3719-4ddf-9f00-709382e1095f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteOrderReduction_EqOneOfIsOfFinOrder

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.FinOrdRedOne PI.FinOrdRedOne.Core
open Matrix Finset
variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
namespace PI.FinOrdRedOne.Core
theorem _root_.solution (D : Matrix n n R) (k : ℕ) :
    (1 + D) ^ (k + 2) = ∑ i ∈ range (k + 1), (k + 2).choose (i + 2) • D ^ (i + 2)
      + (k + 2) • D + 1 := by
  rw [add_comm (1 : Matrix n n R) D, (Commute.one_right D).add_pow,
    Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [one_pow, mul_one, ← nsmul_eq_mul', Nat.choose_one_right, Nat.choose_zero_right,
    pow_zero, pow_one, one_smul, zero_add]
end PI.FinOrdRedOne.Core
