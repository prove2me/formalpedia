-- Prove2me | solution 1 for PI.AmpRootJacW.invC_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:19:14.84832+00:00
-- url     : https://prove2.me/submissions/76780566-432d-430e-a591-9267c9124cc6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RootSubgroupBasics_TriShear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RootSubgroupJacobian_SUpPowEqZero
import Theorems.Thm_PI_AmpRootJacW_vM_at

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
noncomputable section
open PI PI.AmpRootJacW
variable {n : ℕ}
variable (S : Finset (Fin n × Fin n))
namespace PI.AmpRootJacW
theorem _root_.solution (hS : ∀ q ∈ S, q.1 < q.2) (v : S → ℂ) (q : S) : invC S v q = -(v q + hSh S q v) := by
  unfold invC gInv hSh
  rw [Matrix.sum_apply, Finset.sum_range_succ', Finset.sum_range_succ']
  have hq : q.1.1 ≠ q.1.2 := ne_of_lt (hS q.1 q.2)
  simp only [pow_zero, zero_add, pow_one, add_zero, Matrix.one_apply_ne hq, Matrix.neg_apply, vM_at]
  ring
end PI.AmpRootJacW
