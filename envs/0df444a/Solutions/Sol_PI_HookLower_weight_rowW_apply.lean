-- Prove2me | solution 1 for PI.HookLower.weight_rowW_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:43:10.872605+00:00
-- url     : https://prove2.me/submissions/a096891b-f6a3-4c8c-9f9b-06f32f4c5e92

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
theorem _root_.solution {N : ℕ} (m : Fin N × Fin N →₀ ℕ) (a : Fin N) :
    (Finsupp.weight (rowW N N) m) a = ∑ b : Fin N, m (a, b) := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by intro i; simp)]
  rw [Finset.sum_apply, Fintype.sum_prod_type]
  simp only [Pi.smul_apply, rowW, smul_eq_mul, Pi.single_apply]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp
end PI.HookLower
