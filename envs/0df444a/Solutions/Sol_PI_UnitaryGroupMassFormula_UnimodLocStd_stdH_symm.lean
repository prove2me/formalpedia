-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.stdH_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:47:38.77892+00:00
-- url     : https://prove2.me/submissions/a63149f5-13a3-492d-a2bb-da1e93765239

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_SatStdOfAll
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_StdHSingleZero
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_stdH_apply


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
theorem _root_.solution (L : PeriodPair) (x y : m → ℂ) : stdH L m y x = conj (stdH L m x y) := by
  rw [stdH_apply, stdH_apply, map_mul, map_inv₀, Complex.conj_ofReal, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, Complex.conj_conj, mul_comm]
end PI.UnitaryGroupMassFormula.UnimodLocStd
