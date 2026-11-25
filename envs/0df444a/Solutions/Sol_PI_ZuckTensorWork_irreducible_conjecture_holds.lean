-- Prove2me | solution 1 for PI.ZuckTensorWork.irreducible_conjecture_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:28:56.120293+00:00
-- url     : https://prove2.me/submissions/1d40819e-87bb-4a04-bed2-a1ef86b92053

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_PeriodIntegrals_ZuckTensor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_DualDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_DualChoice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_ConjRep
import Theorems.Thm_P2M_PI_ZuckTensorWork_revM_mem_UJset__7a93c3174ea3
import Theorems.Thm_PI_ZuckTensorWork_sigC_revM_mk
import Theorems.Thm_PI_ZuckTensorWork_cjSub_cjSubInv
import Theorems.Thm_PI_ZuckTensorWork_cjSub_bot
import Theorems.Thm_PI_ZuckTensorWork_cjSub_top

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
namespace PI.ZuckTensorWork
theorem _root_.solution : IrredConj := by
  intro n ε H _ _ σ hirr S hS hstab
  have hS' : IsClosed (cjSubInv S : Set H) := hS
  have hstab' : ∀ g ∈ UJset ε, ∀ v ∈ cjSubInv S, σ g v ∈ cjSubInv S := by
    intro g hg v hv
    have := hstab (revM g) (revM_mem_UJset' hg) (Cj.mk v) hv
    rw [sigC_revM_mk] at this
    exact this
  rcases hirr _ hS' hstab' with h0 | h0
  · left; rw [← cjSub_cjSubInv S, h0, cjSub_bot]
  · right; rw [← cjSub_cjSubInv S, h0, cjSub_top]
end PI.ZuckTensorWork
