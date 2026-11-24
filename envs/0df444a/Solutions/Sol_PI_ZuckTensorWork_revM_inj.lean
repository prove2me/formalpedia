-- Prove2me | solution 1 for PI.ZuckTensorWork.revM_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:25:48.390099+00:00
-- url     : https://prove2.me/submissions/6f921e5e-c504-4dd7-8bc3-6bbf9b724905

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_PeriodIntegrals_ZuckTensor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_DualDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_DualChoice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_ConjRep
import Theorems.Thm_PI_ZuckTensorWork_revM_revM

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
variable {n : ℕ}
namespace PI.ZuckTensorWork
theorem _root_.solution {a b : Matrix (Fin n) (Fin n) ℂ} : revM a = revM b ↔ a = b := by
  constructor
  · intro h
    have := congrArg revM h
    rwa [revM_revM, revM_revM] at this
  · intro h; rw [h]
end PI.ZuckTensorWork
