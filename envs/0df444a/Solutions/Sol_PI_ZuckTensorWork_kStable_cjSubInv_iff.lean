-- Prove2me | solution 1 for PI.ZuckTensorWork.kStable_cjSubInv_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:48:45.37064+00:00
-- url     : https://prove2.me/submissions/7a6a78e7-1b22-4858-82ba-2e5d35fea48a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_PeriodIntegrals_ZuckTensor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_DualDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_DualChoice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_ConjRep
import Theorems.Thm_PI_ZuckTensorWork_revM_mem_Kset
import Theorems.Thm_P2M_PI_ZuckTensorWork_revM_mem_Kset__b96cad11e318
import Theorems.Thm_PI_ZuckTensorWork_sigC_revM_mk

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
theorem _root_.solution (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ (Cj H)) :
    IsKStableOn ε σ (cjSubInv S) ↔ IsKStableOn (revE ε) (sigC σ) S := by
  constructor
  · intro h g hg x hx
    exact h (revM g) (revM_mem_Kset hg) (Cj.un x) hx
  · intro h g hg x hx
    have := h (revM g) (revM_mem_Kset' hg) (Cj.mk x) hx
    rw [sigC_revM_mk] at this
    exact this
end PI.ZuckTensorWork
