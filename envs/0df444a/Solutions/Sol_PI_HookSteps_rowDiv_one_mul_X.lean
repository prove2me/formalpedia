-- Prove2me | solution 1 for PI.HookSteps.rowDiv_one_mul_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:09:47.274178+00:00
-- url     : https://prove2.me/submissions/486b270a-152b-48ac-9543-99d58f5dde3e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_DetShiftNormOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LGradedLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFockqLemmas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_DetShift
import Theorems.Thm_PI_HookSteps_rowGen_coeff_zero
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open PI PI.HookSteps
variable {N : ℕ}
namespace PI.HookSteps
theorem _root_.solution (a b : Fin N) (p : MvPolynomial (Fin N × Fin N) ℚ) (v : Fin N × Fin N) :
    rowDiv ℚ a b 1 (p * X v) = rowDiv ℚ a b 1 p * X v + p * (if v.1 = b then X (a, v.2) else 0) := by
  have hX : rowGen ℚ a b (X v : MvPolynomial (Fin N × Fin N) ℚ) = Polynomial.C (X v) +
      (if v.1 = b then Polynomial.X * Polynomial.C (X (a, v.2)) else 0) := by
    simp only [rowGen, MvPolynomial.aeval_X]
  have h0 := rowGen_coeff_zero a b p
  simp only [rowDiv, map_mul, hX, Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ, Finset.sum_range_zero, zero_add, h0]
  split_ifs with h <;> simp [Polynomial.coeff_C, Polynomial.coeff_X_mul, add_comm]
end PI.HookSteps
