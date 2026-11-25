-- Prove2me | solution 1 for PI.OddDualWeyl.EvA.sgn_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:57:36.288116+00:00
-- url     : https://prove2.me/submissions/002da788-09d6-450c-9a39-bcf2e391605d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_AevalMulHomog
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_EvalDuality
import Theorems.Thm_PI_OddDualWeyl_EvA_det_revCol

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
theorem _root_.solution (m : ℕ) : sgnK K m * sgnK K m = 1 := by
  have h : PI.OddDualWeyl.revCol (PI.OddDualWeyl.revCol (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) K)) = 1 := by
    ext i j
    simp only [PI.OddDualWeyl.revCol, Matrix.submatrix_apply]
    rw [Fin.rev_rev]
    all_goals rfl
  have h2 := det_revCol (PI.OddDualWeyl.revCol (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) K))
  rw [h, Matrix.det_one] at h2
  exact h2.symm
end PI.OddDualWeyl.EvA
