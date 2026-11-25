-- Prove2me | solution 1 for P2M_PI_UnitaryGroupMassFormula_LCG_ap_hP__62d51219ff0c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:54:39.903676+00:00
-- url     : https://prove2.me/submissions/1d3b11c2-d828-4b81-8f64-fb231113007b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_SepDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeSizeContinuity_GramLowOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_ArchPlace

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
variable (I : Formalism.MainNotions.S.AutInst)
namespace PI.UnitaryGroupMassFormula.LCG
theorem _root_.solution (v : InfinitePlace I.F) : (I.P v)⁻¹ * I.P v = 1 := by
  exact Matrix.nonsing_inv_mul (I.P v) ((Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v))
end PI.UnitaryGroupMassFormula.LCG
