-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.rep_omega2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:07:24.215906+00:00
-- url     : https://prove2.me/submissions/bf4dbc92-9414-4628-80f8-becde069800b

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
theorem _root_.solution : (cmL a b d ha hd lam hlam).ω₂ = lam * cmTheta b d := rfl
end PI.UnitaryGroupMassFormula.UnimodLocStd
