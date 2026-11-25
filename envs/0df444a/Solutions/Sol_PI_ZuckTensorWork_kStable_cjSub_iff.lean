-- Prove2me | solution 1 for PI.ZuckTensorWork.kStable_cjSub_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:56:59.856121+00:00
-- url     : https://prove2.me/submissions/e9d64043-2395-4683-bccf-352e5c959c45

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_PeriodIntegrals_ZuckTensor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_DualDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_DualChoice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_ConjRep
import Theorems.Thm_PI_ZuckTensorWork_cjSubInv_cjSub
import Theorems.Thm_PI_ZuckTensorWork_kStable_cjSubInv_iff

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
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {n : ℕ} {ε : Fin n → Bool}
namespace PI.ZuckTensorWork
theorem _root_.solution (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H) :
    IsKStableOn ε σ S ↔ IsKStableOn (revE ε) (sigC σ) (cjSub S) := by
  rw [← kStable_cjSubInv_iff, cjSubInv_cjSub]
end PI.ZuckTensorWork
