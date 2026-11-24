-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LCG.ap_hP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:56:10.013725+00:00
-- url     : https://prove2.me/submissions/9f1d825c-0500-489a-9b2f-2a0788b82c65

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
theorem _root_.solution (v : InfinitePlace I.F) : I.P v * (I.P v)⁻¹ = 1 := by
  exact Matrix.mul_nonsing_inv (I.P v) ((Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v))
end PI.UnitaryGroupMassFormula.LCG
