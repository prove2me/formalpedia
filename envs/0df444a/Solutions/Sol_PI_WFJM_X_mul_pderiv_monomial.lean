-- Prove2me | solution 1 for PI.WFJM.X_mul_pderiv_monomial
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:32:09.491593+00:00
-- url     : https://prove2.me/submissions/4cb653b3-424a-43cc-a6d2-093193c2b02f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_JointMultOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LoweringPartRightActionInlInr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action
open PI PI.WFJM
open MvPolynomial
namespace PI.WFJM
theorem _root_.solution {σ : Type*} (i : σ) (α : σ →₀ ℕ) (c : ℂ) :
    X i * pderiv i (monomial α c) = ((α i : ℕ) : ℂ) • monomial α c := by
  rw [pderiv_monomial]
  by_cases h : α i = 0
  · simp [h]
  · rw [X, monomial_mul, one_mul,
      add_tsub_cancel_of_le (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr h)),
      smul_monomial, smul_eq_mul, mul_comm c]
end PI.WFJM
