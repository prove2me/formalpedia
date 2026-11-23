-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.CntFormula.isInt_O
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:44:00.003811+00:00
-- url     : https://prove2.me/submissions/a84b92d8-d4ce-43a9-935a-7bf69f3d6199

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CountingFormula_IsIntIntCast

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.CntFormula
open NumberField
variable {K : Type} [Field K] [NumberField K]
namespace PI.UnitaryGroupMassFormula.CntFormula
theorem _root_.solution (o : 𝓞 K) : IsIntegral ℤ (algebraMap (𝓞 K) K o) := o.2
end PI.UnitaryGroupMassFormula.CntFormula
