-- Prove2me | solution 1 for PI.WFJM.Shape.length_lpos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:50:09.147348+00:00
-- url     : https://prove2.me/submissions/b1808228-16ae-45dc-9a1d-8bdc78e10d71

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_GlobalTheory
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ShapeFromFacts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action
open PI PI.WFJM PI.WFJM.Shape
open PI.FJM
variable {n : ℕ}
namespace PI.WFJM.Shape
theorem _root_.solution {m : ℕ} (α : Fin m → ℕ) : (lpos α).length = m := by simp [lpos]
end PI.WFJM.Shape
