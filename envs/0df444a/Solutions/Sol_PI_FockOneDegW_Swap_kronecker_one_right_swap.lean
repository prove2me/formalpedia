-- Prove2me | solution 1 for PI.FockOneDegW.Swap.kronecker_one_right_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:40:07.742928+00:00
-- url     : https://prove2.me/submissions/e85b9505-3a70-4263-90eb-15d44af32336

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
theorem _root_.solution (Y : Mat r s) :
    ((Matrix.kroneckerMapBilinear (LinearMap.mul ℂ ℂ)) (1 : Mat p q) Y).submatrix
        (sw p q r s).symm (sw p q r s).symm =
      (Matrix.kroneckerMapBilinear (LinearMap.mul ℂ ℂ)).flip (1 : Mat p q) Y := by
  ext ⟨b, a⟩ ⟨b', a'⟩
  simp [Matrix.kroneckerMapBilinear_apply_apply, Matrix.kroneckerMap_apply, mul_comm]
end PI.FockOneDegW.Swap
