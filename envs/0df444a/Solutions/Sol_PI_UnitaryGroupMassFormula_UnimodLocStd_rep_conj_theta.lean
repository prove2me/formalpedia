-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.rep_conj_theta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:07:30.372332+00:00
-- url     : https://prove2.me/submissions/39134cb1-cd5a-441a-b6ef-0c0bdc5dbc6c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepArith

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
namespace PI.UnitaryGroupMassFormula.UnimodLocStd
theorem _root_.solution : conj (cmTheta b d) = ((b : ℂ) - Complex.I * ((Real.sqrt d : ℝ) : ℂ)) / 2 := by
  simp only [cmTheta, map_div₀, map_add, map_mul, map_intCast, Complex.conj_I, Complex.conj_ofReal,
    map_ofNat]
  ring
end PI.UnitaryGroupMassFormula.UnimodLocStd
