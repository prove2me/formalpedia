-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCost.ZI.isOpen_det
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:50:34.264118+00:00
-- url     : https://prove2.me/submissions/fa80be49-c9e5-4642-ba1f-047397d7aad7

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_ZIterA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_ZIterB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCost PI.UnitaryGroupMassFormula.UsCost.ZI
variable (s : ℕ)
namespace PI.UnitaryGroupMassFormula.UsCost.ZI
theorem _root_.solution : IsOpen {Z : Fin s → Fin s → ℂ | (Matrix.of Z).det ≠ 0} :=
  isOpen_ne_fun (Continuous.matrix_det (by exact continuous_id)) continuous_const
end PI.UnitaryGroupMassFormula.UsCost.ZI
