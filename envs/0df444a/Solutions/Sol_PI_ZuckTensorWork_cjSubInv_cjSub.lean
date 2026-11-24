-- Prove2me | solution 1 for PI.ZuckTensorWork.cjSubInv_cjSub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:18:04.467724+00:00
-- url     : https://prove2.me/submissions/62399aed-5e5a-47f5-b2f9-2212ed26856f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_PeriodIntegrals_ZuckTensor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_DualDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_DualChoice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_ConjRep

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
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {n : ℕ}
namespace PI.ZuckTensorWork
theorem _root_.solution (S : Submodule ℂ H) : cjSubInv (cjSub S) = S := by
  ext x; exact Iff.rfl
end PI.ZuckTensorWork
