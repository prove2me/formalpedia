-- Prove2me | solution 1 for PIW.HCFdeg.pi_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:29:11.689695+00:00
-- url     : https://prove2.me/submissions/4a93dc69-6140-4190-ad26-0d29ea42c6ac

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_FormalDegreeFromOrthogonality
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_IntegrableCf
import Theorems.Thm_PIW_HCFdeg_inner_pi

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
theorem _root_.solution (π : G →* (H →L[ℂ] H)) (hiso : ∀ g v, ‖π g v‖ = ‖v‖) (g : G) (v w : H) :
    ⟪w, π g⁻¹ v⟫_ℂ = star ⟪v, π g w⟫_ℂ := by
  have hv : π g (π g⁻¹ v) = v := by
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one, ContinuousLinearMap.one_apply]
  rw [← inner_pi π hiso g w (π g⁻¹ v), hv]
  exact (inner_conj_symm _ _).symm
end PIW.HCFdeg
