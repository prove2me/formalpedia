-- Prove2me | solution 1 for PI.Mk.dvd_sum_eval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:51:32.137193+00:00
-- url     : https://prove2.me/submissions/551a09f4-8f5e-45c2-9111-71ed79b2e5e9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_Minkowski
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinkowskiBound_PowerSumStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinkowskiBound_Assemble
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinkowskiBound_MinkowskiBoundOfSteps

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.Mk
open Finset Polynomial
namespace PI.Mk
theorem _root_.solution (hb : PowerSumStep) (N : ℕ)
    (P : Subgroup (Matrix.GeneralLinearGroup (Fin N) ℤ)) [Fintype P] (f : ℤ[X]) :
    (Fintype.card P : ℤ) ∣ ∑ g : P, f.eval (Matrix.trace
      ((g : Matrix.GeneralLinearGroup (Fin N) ℤ) : Matrix (Fin N) (Fin N) ℤ)) := by
  simp_rw [eval_eq_sum_range]
  rw [Finset.sum_comm]
  apply Finset.dvd_sum
  intro k _
  rw [← Finset.mul_sum]
  exact Dvd.dvd.mul_left (hb N P k) _
end PI.Mk
