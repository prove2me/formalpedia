-- Prove2me | solution 1 for PI.OddDualWeyl.revCol_one_mul_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:59:52.696244+00:00
-- url     : https://prove2.me/submissions/cf903485-91f8-4f79-bcca-5efaabf51d24

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_RevColOneTranspose
import Theorems.Thm_PI_OddDualWeyl_revCol_eq

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
theorem _root_.solution {m : ℕ} : (revCol (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) K)) * revCol 1 = 1 := by
  rw [← revCol_eq]
  ext i j
  simp only [revCol, submatrix_apply]
  rw [Fin.rev_rev]
  rfl
end PI.OddDualWeyl
