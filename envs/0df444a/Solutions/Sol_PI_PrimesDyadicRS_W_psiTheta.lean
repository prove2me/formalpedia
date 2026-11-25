-- Prove2me | solution 1 for PI.PrimesDyadicRS.W.psiTheta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:05:29.69752+00:00
-- url     : https://prove2.me/submissions/83ae0142-684b-4d15-bb8d-bfb179b9cdc5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PrimesDyadicRS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_ThetaDiff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_FloorHalf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_ClaimOfTwo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.PrimesDyadicRS PI.PrimesDyadicRS.W
namespace PI.PrimesDyadicRS.W
theorem _root_.solution : PsiTheta := by
  intro x hx
  have h := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi x
  have e : Real.sqrt x = x ^ ((2 : ℝ)⁻¹) := by rw [Real.sqrt_eq_rpow]; norm_num
  have m3 : Chebyshev.psi (x ^ ((3 : ℝ)⁻¹)) ≤ Chebyshev.psi (x ^ ((2 : ℝ)⁻¹)) :=
    Chebyshev.psi_mono (Real.rpow_le_rpow_of_exponent_le hx (by norm_num))
  have m5 : Chebyshev.psi (x ^ ((5 : ℝ)⁻¹)) ≤ Chebyshev.psi (x ^ ((2 : ℝ)⁻¹)) :=
    Chebyshev.psi_mono (Real.rpow_le_rpow_of_exponent_le hx (by norm_num))
  rw [e]
  linarith
end PI.PrimesDyadicRS.W
