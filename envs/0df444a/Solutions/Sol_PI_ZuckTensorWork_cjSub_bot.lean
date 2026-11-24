-- Prove2me | solution 1 for PI.ZuckTensorWork.cjSub_bot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:17:14.88417+00:00
-- url     : https://prove2.me/submissions/2f9cf18e-161b-4d0a-bb3b-eb675418ddd7

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
theorem _root_.solution : cjSub (⊥ : Submodule ℂ H) = ⊥ := by
  ext x
  show Cj.un x ∈ (⊥ : Submodule ℂ H) ↔ x ∈ (⊥ : Submodule ℂ (Cj H))
  rw [Submodule.mem_bot, Submodule.mem_bot]; exact Iff.rfl
end PI.ZuckTensorWork
