-- Prove2me | solution 1 for PI.WMI.lowerInv_e_mul_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:10:55.2172+00:00
-- url     : https://prove2.me/submissions/00abe6cb-bf6e-4e5f-851d-39935b822351

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
theorem _root_.solution (r s : ℝ) (m : ℕ) :
    lowerInv_e r * lowerInv_e s ^ m = lowerInv_e (r + m * s) := by
  unfold lowerInv_e
  rw [← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1; push_cast; ring
end PI.WMI
