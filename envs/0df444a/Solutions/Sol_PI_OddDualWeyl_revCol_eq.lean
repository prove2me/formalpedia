-- Prove2me | solution 1 for PI.OddDualWeyl.revCol_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:27:40.736504+00:00
-- url     : https://prove2.me/submissions/a068fcb4-442d-4ab3-91b4-bc69d88150c3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_RevColOneTranspose

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
open PI PI.OddDualWeyl
variable {K : Type} [Field K]
namespace PI.OddDualWeyl
theorem _root_.solution {m : ℕ} (A : Matrix (Fin (m + 1)) (Fin (m + 1)) K) : revCol A = A * revCol 1 := by
  ext i j
  simp [revCol, Matrix.mul_apply, Matrix.one_apply]
end PI.OddDualWeyl
