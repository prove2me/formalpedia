-- Prove2me | solution 1 for PI.OddDualWeyl.Red.rowAct_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:32:07.645068+00:00
-- url     : https://prove2.me/submissions/04f7725c-180f-4417-b201-3357902ed9f9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_AevalMulHomog

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
open PI PI.OddDualWeyl PI.OddDualWeyl.Red
variable {R : Type*} [CommRing R] {k : ℕ}
namespace PI.OddDualWeyl.Red
theorem _root_.solution (g : Matrix (Fin k) (Fin k) R) : rowAct R g = sbs (cM g * genM R k) := by
  apply MvPolynomial.algHom_ext
  intro v
  simp [PI.OddDualWeyl.rowAct, sbs, cM, PI.OddDualWeyl.genM, Matrix.mul_apply]
end PI.OddDualWeyl.Red
