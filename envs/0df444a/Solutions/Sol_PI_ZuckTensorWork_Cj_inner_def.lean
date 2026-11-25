-- Prove2me | solution 1 for PI.ZuckTensorWork.Cj.inner_def
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:17:17.891686+00:00
-- url     : https://prove2.me/submissions/d95cadf8-7286-48a3-8baa-d7233ec99a40

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_PeriodIntegrals_ZuckTensor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_DualDefs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped InnerProductSpace
noncomputable section
open PI PI.ZuckTensorWork
open PI.UpqRep PI.ZuckTensor
open PI.ZuckTensorWork.Cj
variable {H : Type}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]
namespace PI.ZuckTensorWork.Cj
theorem _root_.solution (x y : Cj H) : ⟪x, y⟫_ℂ = ⟪un y, un x⟫_ℂ := rfl
end PI.ZuckTensorWork.Cj
