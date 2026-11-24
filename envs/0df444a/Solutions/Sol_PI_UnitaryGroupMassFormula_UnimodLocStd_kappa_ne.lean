-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.kappa_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:14:40.373839+00:00
-- url     : https://prove2.me/submissions/0e01c65f-2ede-4186-8897-da2ed694f873

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_IsKTheta
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_CommOfBounded
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_area_eq
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_detD_ne
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
theorem _root_.solution (L : PeriodPair) (hlam : lam ≠ 0) : kappa L lam ≠ 0 := by
  have harea : ((area L : ℝ) : ℂ) ≠ 0 := by
    rw [area_eq]
    exact Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr (detD_ne L))
  have hc : conj lam ≠ 0 := by rwa [Ne, map_eq_zero]
  simp only [kappa]
  exact mul_ne_zero (mul_ne_zero hlam hc) (inv_ne_zero harea)
end PI.UnitaryGroupMassFormula.UnimodLocStd
