-- Prove2me | solution 1 for PIW.HCFdeg.pi_mul_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:32:24.745802+00:00
-- url     : https://prove2.me/submissions/cd5cfaf0-a3c7-499f-913e-099021bcb816

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_FormalDegreeFromOrthogonality
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_IntegrableCf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.HCFdeg
open MeasureTheory
open scoped InnerProductSpace ComplexConjugate
variable {G : Type} [Group G] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
namespace PIW.HCFdeg
theorem _root_.solution (π : G →* (H →L[ℂ] H)) (g h : G) (x : H) : π (g * h) (π h⁻¹ x) = π g x := by
  rw [map_mul, ContinuousLinearMap.mul_apply, ← ContinuousLinearMap.mul_apply (π h), ← map_mul, mul_inv_cancel, map_one,
    ContinuousLinearMap.one_apply]
end PIW.HCFdeg
