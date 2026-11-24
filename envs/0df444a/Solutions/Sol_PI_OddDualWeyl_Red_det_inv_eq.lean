-- Prove2me | solution 1 for PI.OddDualWeyl.Red.det_inv_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:12:32.303799+00:00
-- url     : https://prove2.me/submissions/cb4c6337-daca-42ec-8fb6-094d6222ad0a

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
variable {K : Type*} [Field K] {k : ℕ}
namespace PI.OddDualWeyl.Red
theorem _root_.solution (g : Matrix (Fin k) (Fin k) K) : (g⁻¹).det = (g.det)⁻¹ := by
  first
  | rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  | simp [Matrix.det_nonsing_inv]
  | simp [Matrix.det_inv]
end PI.OddDualWeyl.Red
