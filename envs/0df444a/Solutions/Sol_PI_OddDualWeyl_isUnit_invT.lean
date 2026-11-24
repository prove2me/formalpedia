-- Prove2me | solution 1 for PI.OddDualWeyl.isUnit_invT
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:32:09.222831+00:00
-- url     : https://prove2.me/submissions/6a15dbd6-1634-410b-b6c1-3f2fac6a18e3

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
theorem _root_.solution {n : ℕ} {g : Matrix (Fin n) (Fin n) K} (hg : IsUnit g.det) : IsUnit ((g⁻¹)ᵀ).det := by
  rw [det_transpose]
  exact isUnit_nonsing_inv_det g hg
end PI.OddDualWeyl
