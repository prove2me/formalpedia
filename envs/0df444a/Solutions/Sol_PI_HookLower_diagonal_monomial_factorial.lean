-- Prove2me | solution 1 for PI.HookLower.diagonal_monomial_factorial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:37:25.176937+00:00
-- url     : https://prove2.me/submissions/42d80603-e8e8-4905-a9dc-716da2bb4dd2

import Definitions.Def_Formalism_PeriodIntegrals_HookBound
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_DiagonalMonomialFactorial
import Theorems.Thm_PI_HookLower_isDiag_diagonal_monomial
import Theorems.Thm_PI_HookLower_diagonal_monomial_apply
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
    (∏ k ∈ (M0 ν).support, ((M0 ν) k).factorial) = ∏ l, (ν l).factorial := by
  classical
  rw [Finset.prod_subset (Finset.subset_univ _) (fun k _ hk => by
    rw [Finsupp.notMem_support_iff.1 hk]; rfl)]
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [Finset.prod_eq_single a]
  · rw [diagonal_monomial_apply ν hν a]
  · intro b _ hb
    rw [isDiag_diagonal_monomial ν (a, b) (Ne.symm hb)]
    rfl
  · simp
end PI.HookLower
