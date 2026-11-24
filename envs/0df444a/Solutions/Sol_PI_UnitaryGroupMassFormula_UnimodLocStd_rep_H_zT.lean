-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.rep_H_zT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:25:29.329831+00:00
-- url     : https://prove2.me/submissions/124f7ddc-602b-43b9-a755-8b9615a7d527

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepHSelfInt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepExact
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepSingleSat

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
variable (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0)
  (m : Type) [Fintype m] [DecidableEq m]
namespace PI.UnitaryGroupMassFormula.UnimodLocStd
theorem _root_.solution (T : Finset m) {z y : m → ℂ} (hz : ∀ j ∈ T, z j = 0) :
    stdH (cmL a b d ha hd lam hlam) m z (zT T y) = stdH (cmL a b d ha hd lam hlam) m z y := by
  simp only [stdH, matH, LinearMap.mk₂'ₛₗ_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  unfold zT
  by_cases hj : j ∈ T
  · rw [if_pos hj, map_zero, mul_zero]
    by_cases hij : i = j
    · subst hij
      rw [hz i hj, zero_mul, zero_mul]
    · rw [Matrix.smul_apply, Matrix.one_apply_ne hij, smul_zero, mul_zero, zero_mul]
  · rw [if_neg hj]
end PI.UnitaryGroupMassFormula.UnimodLocStd
