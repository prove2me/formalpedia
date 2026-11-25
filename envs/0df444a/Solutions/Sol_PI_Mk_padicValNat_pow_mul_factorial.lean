-- Prove2me | solution 1 for PI.Mk.padicValNat_pow_mul_factorial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:52:05.21314+00:00
-- url     : https://prove2.me/submissions/ea0e127e-7048-434a-a01b-dd94a1a773d0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_Minkowski
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinkowskiBound_PowerSumStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinkowskiBound_Assemble
import Theorems.Thm_PI_Mk_term_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.Mk
open Finset
namespace PI.Mk
theorem _root_.solution (N ℓ : ℕ) (hℓ : ℓ.Prime) :
    padicValNat ℓ (ℓ ^ (N / (ℓ - 1)) * (N / (ℓ - 1)).factorial) = PI.minkowskiExp N ℓ := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  set m := N / (ℓ - 1) with hm
  have hmN : m ≤ N := Nat.div_le_self _ _
  have hlog : Nat.log ℓ m < N + 1 := lt_of_le_of_lt (Nat.log_le_self _ _) (Nat.lt_succ_of_le hmN)
  rw [padicValNat.mul (pow_ne_zero _ hℓ.ne_zero) (Nat.factorial_ne_zero _), padicValNat.prime_pow,
    padicValNat_factorial hlog]
  unfold PI.minkowskiExp
  simp_rw [term_eq, ← hm]
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos N)]
  simp
end PI.Mk
