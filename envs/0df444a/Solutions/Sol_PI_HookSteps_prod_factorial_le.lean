-- Prove2me | solution 1 for PI.HookSteps.prod_factorial_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:11:58.077195+00:00
-- url     : https://prove2.me/submissions/1287bed4-ceac-4d57-9874-f9609c740cfd

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_DetShiftNormOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_DiagonalMonomialFactorial
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_ProdFactorialLe
import Theorems.Thm_PI_HookSteps_sum_rev_eq
import Theorems.Thm_PI_HookSteps_factorial_add_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open PI PI.HookSteps
namespace PI.HookSteps
theorem _root_.solution (N : ℕ) (hN : 0 < N) (ν : Fin N → ℕ) (hν : Antitone ν) :
    ∏ i : Fin N, (ν i + (N - 1 - i)).factorial ≤
      (∏ i, (ν i).factorial) * (ν ⟨0, hN⟩ + N) ^ (N * (N - 1) / 2) := by
  have hB : ∀ i : Fin N, ν i + (N - 1 - i) ≤ ν ⟨0, hN⟩ + N := fun i => by
    have := hν (show (⟨0, hN⟩ : Fin N) ≤ i from Nat.zero_le _)
    omega
  calc ∏ i : Fin N, (ν i + (N - 1 - i)).factorial
      ≤ ∏ i : Fin N, ((ν i).factorial * (ν ⟨0, hN⟩ + N) ^ (N - 1 - (i : ℕ))) :=
        Finset.prod_le_prod (fun _ _ => Nat.zero_le _) fun i _ => factorial_add_le _ _ _ (hB i)
    _ = (∏ i, (ν i).factorial) * (ν ⟨0, hN⟩ + N) ^ (N * (N - 1) / 2) := by
        rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, sum_rev_eq]
end PI.HookSteps
