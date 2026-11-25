-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.theta_alpha_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:47:44.468672+00:00
-- url     : https://prove2.me/submissions/7aced230-813b-4b01-a25c-cafcb444642f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_ExistsGoodForm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_SatStdOfAll
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_cmL_omega1
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_cmL_omega2
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
variable {a : ℕ} {b c : ℤ} {d : ℕ} {ha : 0 < a} {hd : 0 < d} {lam : ℂ} {hlam : lam ≠ 0}
variable {m : Type*} [Fintype m] [DecidableEq m]
namespace PI.UnitaryGroupMassFormula.UnimodLocStd
theorem _root_.solution (hn : cmTheta b d * (b - cmTheta b d) = (a : ℂ) * c) (x y : ℤ) :
    cmTheta b d * (lam * ((x * a : ℂ) + y * cmTheta b d)) =
      ((-y * c : ℤ) : ℝ) • (cmL a b d ha hd lam hlam).ω₁ +
        ((x * a + y * b : ℤ) : ℝ) • (cmL a b d ha hd lam hlam).ω₂ := by
  rw [cmL_omega1, cmL_omega2]
  simp only [Complex.real_smul]
  push_cast
  linear_combination (-(lam * y)) * hn
end PI.UnitaryGroupMassFormula.UnimodLocStd
