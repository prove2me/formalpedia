-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LCG.ht_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:51:55.649993+00:00
-- url     : https://prove2.me/submissions/bad784e3-2efd-4fbb-9049-ac7bd90d0c0d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_SepDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeSizeContinuity_LatticeIsometry
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_LatticeIsDiscreteGroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LCG
open PI.LatCountG
namespace PI.UnitaryGroupMassFormula.LCG
theorem _root_.solution (I : Formalism.MainNotions.S.AutInst) {z : I.GA} (s : Sub I z) :
    ht I s = (∏ v, ((gramV I z v s.b).det).re) / (idx I s.B s.b : ℝ) := rfl
end PI.UnitaryGroupMassFormula.LCG
