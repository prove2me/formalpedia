-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.rep_H_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:09:33.325246+00:00
-- url     : https://prove2.me/submissions/b12fa0e2-8844-4120-8019-d5e7c87064e3

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepBasic
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_rep_H_apply

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
variable (L : PeriodPair) (m : Type) [Fintype m] [DecidableEq m]
namespace PI.UnitaryGroupMassFormula.UnimodLocStd
theorem _root_.solution (z w : m → ℂ) : conj (stdH L m z w) = stdH L m w z := by
  rw [rep_H_apply, rep_H_apply, map_mul, map_sum]
  congr 1
  · simp [Complex.conj_ofReal]
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp [mul_comm]
end PI.UnitaryGroupMassFormula.UnimodLocStd
