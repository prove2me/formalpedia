-- Prove2me | solution 1 for PI.OddDualWeyl.EvA.revCol_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:49:00.419821+00:00
-- url     : https://prove2.me/submissions/09c9110b-9221-4ec4-a884-d5a41e438e22

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_AevalMulHomog
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_EvalDuality

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
noncomputable section
open PI PI.OddDualWeyl PI.OddDualWeyl.EvA
open Red
variable {K : Type} [Field K]
namespace PI.OddDualWeyl.EvA
theorem _root_.solution {m : ℕ} (A : Matrix (Fin (m + 1)) (Fin (m + 1)) K) : revCol A = A * revCol 1 := by
  ext i j
  first
  | simp [PI.OddDualWeyl.revCol, Matrix.mul_apply, Matrix.one_apply]
  | (rw [Matrix.mul_apply]; simp [PI.OddDualWeyl.revCol, Matrix.one_apply, Finset.sum_ite_eq, Finset.sum_ite_eq'])
end PI.OddDualWeyl.EvA
