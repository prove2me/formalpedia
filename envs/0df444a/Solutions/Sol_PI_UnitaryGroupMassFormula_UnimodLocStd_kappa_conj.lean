-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.kappa_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:45:55.645342+00:00
-- url     : https://prove2.me/submissions/77a78590-c961-4c23-b7e7-940319377c77

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_IsKTheta
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_CommOfBounded
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
theorem _root_.solution (L : PeriodPair) (lam : ℂ) : conj (kappa L lam) = kappa L lam := by
  simp only [kappa]
  rw [map_mul, map_mul, map_inv₀, Complex.conj_conj, Complex.conj_ofReal]
  ring
end PI.UnitaryGroupMassFormula.UnimodLocStd
