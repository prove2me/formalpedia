-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.two_theta_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:47:46.076536+00:00
-- url     : https://prove2.me/submissions/41456766-909c-4c50-a4fd-5a80aba87242

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RelIdxNeZeroOfLeLeft
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_smulHom_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PI.UnitaryGroupMassFormula.UnimodLocStd.smulHom_apply

set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS
variable {a : ℕ} {b c : ℤ} {d : ℕ}
namespace PI.UnitaryGroupMassFormula.UnimodLocStd
theorem _root_.solution (b : ℤ) {d : ℕ} (hd : 0 < d) : 2 * cmTheta b d - b ≠ 0 := by
  have e : 2 * PI.ULS.cmTheta b d - b = Complex.I * ((Real.sqrt d : ℝ) : ℂ) := by
    simp only [PI.ULS.cmTheta]; ring
  rw [e]
  exact mul_ne_zero Complex.I_ne_zero
    (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by exact_mod_cast hd)).ne')
end PI.UnitaryGroupMassFormula.UnimodLocStd
