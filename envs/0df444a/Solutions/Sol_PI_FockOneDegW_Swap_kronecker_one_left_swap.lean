-- Prove2me | solution 1 for PI.FockOneDegW.Swap.kronecker_one_left_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:40:04.135077+00:00
-- url     : https://prove2.me/submissions/db4d822d-c09b-439a-a40d-9e1e4272d679

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OneDegOfHalves
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OmEDiagMonomial
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_KroneckerOneRightSwap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial
open PI PI.FockOneDegW PI.FockOneDegW.Swap
open PI.FockOneDegW PI.FockOneDegW.Diag
variable {p q r s : ℕ}
namespace PI.FockOneDegW.Swap
theorem _root_.solution (X : Mat p q) :
    ((Matrix.kroneckerMapBilinear (LinearMap.mul ℂ ℂ)).flip (1 : Mat r s) X).submatrix
        (sw p q r s).symm (sw p q r s).symm =
      (Matrix.kroneckerMapBilinear (LinearMap.mul ℂ ℂ)) (1 : Mat r s) X := by
  ext ⟨b, a⟩ ⟨b', a'⟩
  simp [Matrix.kroneckerMapBilinear_apply_apply, Matrix.kroneckerMap_apply, mul_comm]
end PI.FockOneDegW.Swap
