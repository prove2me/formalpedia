-- Prove2me | solution 1 for PI.ZuckTensorWork.Cj.un_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:03:33.637595+00:00
-- url     : https://prove2.me/submissions/d474a8aa-4b6b-44de-81a8-97141a2769ef

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
theorem _root_.solution (c : ℂ) (x : Cj H) : un (c • x) = (starRingEnd ℂ) c • un x := rfl
end PI.ZuckTensorWork.Cj
