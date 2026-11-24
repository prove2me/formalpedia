-- Prove2me | solution 1 for PI.ZuckTensorWork.sigC_revM_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:25:49.496076+00:00
-- url     : https://prove2.me/submissions/30b276ff-5edd-4866-b10f-3a05d2a01551

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_PeriodIntegrals_ZuckTensor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_DualDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_DualChoice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_ConjRep
import Theorems.Thm_PI_ZuckTensorWork_revM_revM
import Theorems.Thm_PI_ZuckTensorWork_sigC_mk

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
theorem _root_.solution (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (g : Matrix (Fin n) (Fin n) ℂ) (x : H) :
    sigC σ (revM g) (Cj.mk x) = Cj.mk (σ g x) := by
  rw [sigC_mk, revM_revM]
end PI.ZuckTensorWork
