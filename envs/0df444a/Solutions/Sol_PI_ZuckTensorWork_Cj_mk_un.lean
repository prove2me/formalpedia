-- Prove2me | solution 1 for PI.ZuckTensorWork.Cj.mk_un
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:03:23.194428+00:00
-- url     : https://prove2.me/submissions/b028ea85-2b8a-4d6b-96a5-4d5de69f05f1

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
namespace PI.ZuckTensorWork.Cj
theorem _root_.solution (x : Cj H) : mk (un x) = x := rfl
end PI.ZuckTensorWork.Cj
