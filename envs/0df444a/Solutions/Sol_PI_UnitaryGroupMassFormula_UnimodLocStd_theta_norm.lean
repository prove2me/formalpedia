-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.theta_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:56:10.098869+00:00
-- url     : https://prove2.me/submissions/c5f9e049-3f91-459f-9f71-97d498d1d78f

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
theorem _root_.solution (h : 4 * (a : ℤ) * c = b ^ 2 + d) :
    cmTheta b d * (b - cmTheta b d) = (a : ℂ) * c := by
  have hs : ((Real.sqrt d : ℝ) : ℂ) ^ 2 = (d : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
    simp
  have hc : (4 : ℂ) * a * c = (b : ℂ) ^ 2 + d := by exact_mod_cast h
  simp only [PI.ULS.cmTheta]
  linear_combination (-(((Real.sqrt d : ℝ) : ℂ) ^ 2) / 4) * Complex.I_sq + (1 / 4 : ℂ) * hs
    + (-1 / 4 : ℂ) * hc
end PI.UnitaryGroupMassFormula.UnimodLocStd
