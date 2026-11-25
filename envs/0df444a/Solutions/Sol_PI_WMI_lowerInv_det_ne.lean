-- Prove2me | solution 1 for PI.WMI.lowerInv_det_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:10:52.141095+00:00
-- url     : https://prove2.me/submissions/91166a33-0fdd-47b1-b975-82213461e43e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_IsPolyMon
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_LowerInv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WMI
open PI.UpqRep Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial Matrix
open scoped InnerProductSpace
namespace PI.WMI
theorem _root_.solution {N : ℕ} (θ : Fin N → ℝ) : (torus θ).det ≠ 0 := by
  unfold torus
  rw [Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => Complex.exp_ne_zero _
end PI.WMI
