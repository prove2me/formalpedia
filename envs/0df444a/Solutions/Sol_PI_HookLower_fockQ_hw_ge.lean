-- Prove2me | solution 1 for PI.HookLower.fockQ_hw_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:53:45.615461+00:00
-- url     : https://prove2.me/submissions/4b53f815-9b50-4835-a175-9f9843989fcb

import Definitions.Def_Formalism_PeriodIntegrals_HookBound
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_DiagonalMonomialFactorial
import Theorems.Thm_PI_HookLower_coeff_diagonal_monomial_hw
import Theorems.Thm_PI_HookLower_diagonal_monomial_factorial
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
open PI PI.HookLower
namespace PI.HookLower
theorem _root_.solution {N : ℕ} (ν : Fin N → ℕ) (hν : Antitone ν) :
    (∏ l, ((ν l).factorial : ℚ)) ≤ fockQ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν) := by
  classical
  have hmem : M0 ν ∈ (hw ℚ le_rfl ν).support := by
    rw [mem_support_iff, coeff_diagonal_monomial_hw]; exact one_ne_zero
  unfold fockQ
  refine le_trans (le_of_eq ?_) (Finset.single_le_sum (f := fun m =>
      coeff m (hw ℚ le_rfl ν) * coeff m (hw ℚ le_rfl ν) *
        ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℚ))
    (fun m _ => mul_nonneg (mul_self_nonneg _) (Nat.cast_nonneg _)) hmem)
  simp only [coeff_diagonal_monomial_hw, one_mul]
  rw [diagonal_monomial_factorial ν hν]
  push_cast
  rfl
end PI.HookLower
