-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCost.ZI.eA_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:50:34.351336+00:00
-- url     : https://prove2.me/submissions/63cc5fd0-dfb3-4449-ad4a-b18d1cd92e48

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
theorem _root_.solution (Z : Fin s → Fin s → ℂ) (v : Fin s → ℂ) : eA s Z v = (Matrix.of Z).mulVec v := rfl
end PI.UnitaryGroupMassFormula.UsCost.ZI
