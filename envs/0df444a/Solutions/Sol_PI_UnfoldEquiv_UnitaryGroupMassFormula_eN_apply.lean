-- Prove2me | solution 1 for PI.UnfoldEquiv.UnitaryGroupMassFormula.eN_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:16:22.02041+00:00
-- url     : https://prove2.me/submissions/f847f8fa-801e-41dd-9cb6-76813b3bf8ee

import Definitions.Def_Formalism_PeriodIntegrals_UnfoldEquiv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnfoldingEquivalence_ExtractFreeFillMatrix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI.UnfoldEquiv PI.UnfoldEquiv.Loc
noncomputable section
open PI PI.UnfoldEquiv PI.UnfoldEquiv.UnitaryGroupMassFormula
variable {k : Type} [CommRing k]
namespace PI.UnfoldEquiv.UnitaryGroupMassFormula
theorem _root_.solution (N i : ℕ) (l : Fin N) : eN k N i l = if l.1 = i then 1 else 0 := rfl
end PI.UnfoldEquiv.UnitaryGroupMassFormula
