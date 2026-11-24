-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.alpha_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:33:29.546053+00:00
-- url     : https://prove2.me/submissions/d8c5a4b6-658b-47f3-8aef-cdd57a41dbed

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
theorem _root_.solution (x y : ℤ) :
    lam * ((x * a : ℂ) + y * cmTheta b d) =
      (x : ℝ) • (cmL a b d ha hd lam hlam).ω₁ + (y : ℝ) • (cmL a b d ha hd lam hlam).ω₂ := by
  rw [cmL_omega1, cmL_omega2]
  simp only [Complex.real_smul]
  push_cast
  ring
end PI.UnitaryGroupMassFormula.UnimodLocStd
