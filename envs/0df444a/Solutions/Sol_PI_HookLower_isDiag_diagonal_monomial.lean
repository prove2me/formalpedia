-- Prove2me | solution 1 for PI.HookLower.isDiag_diagonal_monomial
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:16:23.8278+00:00
-- url     : https://prove2.me/submissions/8f5a1b57-5c58-4ff3-ad02-d0e5baa3e27a

import Definitions.Def_Formalism_PeriodIntegrals_HookBound
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_DiagonalMonomialFactorial
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
theorem _root_.solution {N : ℕ} (ν : Fin N → ℕ) : IsDiag (M0 ν) := by
  classical
  intro v hv
  simp only [M0, diagMono, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]
  refine Finset.sum_eq_zero fun s _ => ?_
  rw [Finset.sum_eq_zero, mul_zero]
  intro p _
  rw [Finsupp.single_apply, if_neg]
  intro h
  subst h
  exact hv rfl
end PI.HookLower
