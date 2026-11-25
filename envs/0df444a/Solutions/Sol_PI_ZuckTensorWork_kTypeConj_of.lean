-- Prove2me | solution 1 for PI.ZuckTensorWork.kTypeConj_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:03:45.627013+00:00
-- url     : https://prove2.me/submissions/273572fd-e0cf-4ffc-8f17-51b56a4337d9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_PeriodIntegrals_ZuckTensor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_DualDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_DualChoice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_ConjRep
import Theorems.Thm_PI_ZuckTensorWork_cjSub_cjSubInv
import Theorems.Thm_PI_ZuckTensorWork_cjSubInv_cjSub
import Theorems.Thm_PI_ZuckTensorWork_cjSub_bot
import Theorems.Thm_PI_ZuckTensorWork_cjSubInv_le_iff
import Theorems.Thm_PI_ZuckTensorWork_cjSub_finiteDimensional
import Theorems.Thm_PI_ZuckTensorWork_isWtOn_sigC_iff
import Theorems.Thm_P2M_PI_ZuckTensorWork_isWtOn_sigC_iff__603798d8d857
import Theorems.Thm_PI_ZuckTensorWork_kStable_cjSubInv_iff
import Theorems.Thm_PI_ZuckTensorWork_kStable_cjSub_iff
import Theorems.Thm_PI_ZuckTensorWork_dualWeight_dualWeight


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
theorem _root_.solution (h : CDomRev) : KTypeConj := by
  intro n ε H _ _ σ Λ S ⟨hfd, hst, hirr, ⟨v, hvS, hv0, hvw⟩, hdom⟩
  refine ⟨(haveI := hfd; cjSub_finiteDimensional S), (kStable_cjSub_iff σ S).mp hst, ?_,
    ⟨Cj.mk v, hvS, hv0, (isWtOn_sigC_iff σ Λ v).mp hvw⟩, ?_⟩
  · intro S' hle hst'
    have hle' : cjSubInv S' ≤ S := by
      rw [← cjSubInv_cjSub S]; exact cjSubInv_le_iff.mpr hle
    rcases hirr _ hle' ((kStable_cjSubInv_iff σ S').mpr hst') with h0 | h0
    · left; rw [← cjSub_cjSubInv S', h0, cjSub_bot]
    · right; rw [← cjSub_cjSubInv S', h0]
  · intro μ x hx hx0 hxw
    have h1 := hdom (revP μ) (Cj.un x) hx hx0 ((isWtOn_sigC_iff' σ μ x).mp hxw)
    have h2 := h n ε (revP μ) Λ h1
    rwa [dualWeight_dualWeight] at h2
end PI.ZuckTensorWork
