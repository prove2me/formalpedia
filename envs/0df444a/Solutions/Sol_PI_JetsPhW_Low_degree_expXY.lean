-- Prove2me | solution 1 for PI.JetsPhW.Low.degree_expXY
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:34:02.477822+00:00
-- url     : https://prove2.me/submissions/290fc68c-eaf4-4030-a638-4adac1b5153b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_CoeffSubstOfDegreeEqOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.JetsPhW PI.JetsPhW.Low
variable {K : Type*} [CommRing K]
namespace PI.JetsPhW.Low
theorem _root_.solution : Finsupp.degree bivariateExponentMonomial = 2 := by
  rw [map_add, Finsupp.degree_single, Finsupp.degree_single]
end PI.JetsPhW.Low
