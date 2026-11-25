-- Prove2me | solution 1 for PI.HookLower.diagonal_monomial_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:30:59.786884+00:00
-- url     : https://prove2.me/submissions/cc73a034-e64a-4194-94c8-a9dcd13eb37d

import Definitions.Def_Formalism_PeriodIntegrals_HookBound
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_DiagonalMonomialFactorial
import Theorems.Thm_PI_HookLower_isDiag_diagonal_monomial
import Theorems.Thm_PI_HookLower_coeff_diagonal_monomial_hw
import Theorems.Thm_PI_HookLower_weight_rowW_apply
import Theorems.Thm_Formalism_GradedWeylDivisibility_hwRowWeight
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
theorem _root_.solution {N : ℕ} (ν : Fin N → ℕ) (hν : Antitone ν) (a : Fin N) : M0 ν (a, a) = ν a := by
  classical
  have hmem : coeff (M0 ν) (hw ℚ le_rfl ν) ≠ 0 := by rw [coeff_diagonal_monomial_hw]; exact one_ne_zero
  have hw8 := hwRowWeight ℚ N N le_rfl ν hν hmem
  have h1 := congrFun hw8 a
  rw [weight_rowW_apply, Finset.sum_eq_single a] at h1
  · rw [h1]
    simp [rowNu]
  · intro b _ hb
    exact isDiag_diagonal_monomial ν (a, b) (Ne.symm hb)
  · simp
end PI.HookLower
