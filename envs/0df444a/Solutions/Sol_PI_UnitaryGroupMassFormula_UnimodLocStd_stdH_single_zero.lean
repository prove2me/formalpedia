-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.stdH_single_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:48:36.863195+00:00
-- url     : https://prove2.me/submissions/7e266a40-afd5-4f0a-a8aa-2c60f2160d18

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_SatStdOfAll
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_StdHSingleZero
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_smulHom_apply
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_stdH_apply
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
theorem _root_.solution (L : PeriodPair) (j : m) (w : ℂ) {z : m → ℂ} (hz : z j = 0) :
    stdH L m (Pi.single j w) z = 0 := by
  rw [stdH_apply]
  have hsum : ∑ i, (Pi.single j w : m → ℂ) i * conj (z i) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases h : i = j
    · subst h
      rw [hz, map_zero, mul_zero]
    · simp [h]
  rw [hsum, zero_mul]
end PI.UnitaryGroupMassFormula.UnimodLocStd
