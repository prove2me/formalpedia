-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.isKv_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:45:34.421568+00:00
-- url     : https://prove2.me/submissions/6f862c8e-a0bd-4e80-9ab1-e81c936351d4

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_IsKTheta
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_CommOfBounded
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_isK_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS
variable {a : ℕ} {b c : ℤ} {d : ℕ} {ha : 0 < a} {hd : 0 < d} {lam : ℂ} {hlam : lam ≠ 0}
variable {m : Type*} [Fintype m] [DecidableEq m]
namespace PI.UnitaryGroupMassFormula.UnimodLocStd
theorem _root_.solution {e : ℤ} (hn : cmTheta b d * (b - cmTheta b d) = (e : ℂ)) {t : ℂ} {v : m → ℂ}
    (ht : IsK b d t) (hv : IsKv b d lam v) : IsKv b d lam (t • v) := by
  intro i
  rw [Pi.smul_apply, smul_eq_mul, mul_div_assoc]
  exact isK_mul hn ht (hv i)
end PI.UnitaryGroupMassFormula.UnimodLocStd
