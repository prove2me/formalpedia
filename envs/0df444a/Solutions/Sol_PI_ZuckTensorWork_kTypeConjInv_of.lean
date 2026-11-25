-- Prove2me | solution 1 for PI.ZuckTensorWork.kTypeConjInv_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:03:42.973851+00:00
-- url     : https://prove2.me/submissions/5dc68888-349f-4744-93a1-07a82bdf6472

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_PeriodIntegrals_ZuckTensor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_DualDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_DualChoice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_ConjRep
import Theorems.Thm_PI_ZuckTensorWork_cjSub_cjSubInv
import Theorems.Thm_PI_ZuckTensorWork_cjSubInv_cjSub
import Theorems.Thm_PI_ZuckTensorWork_cjSubInv_bot
import Theorems.Thm_PI_ZuckTensorWork_cjSub_le_iff
import Theorems.Thm_PI_ZuckTensorWork_cjSubInv_finiteDimensional
import Theorems.Thm_PI_ZuckTensorWork_isWtOn_sigC_iff
import Theorems.Thm_P2M_PI_ZuckTensorWork_isWtOn_sigC_iff__603798d8d857
import Theorems.Thm_PI_ZuckTensorWork_kStable_cjSubInv_iff
import Theorems.Thm_PI_ZuckTensorWork_kStable_cjSub_iff
import Theorems.Thm_PI_ZuckTensorWork_dualWeight_dualWeight
import Theorems.Thm_PI_ZuckTensorWork_revE_revE


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
theorem _root_.solution (h : CDomRev) : KTypeConjInv := by
  intro n ε H _ _ σ Λ S ⟨hfd, hst, hirr, ⟨x, hxS, hx0, hxw⟩, hdom⟩
  refine ⟨(haveI := hfd; cjSubInv_finiteDimensional S), (kStable_cjSubInv_iff σ S).mpr hst, ?_,
    ⟨Cj.un x, hxS, hx0, (isWtOn_sigC_iff' σ Λ x).mp hxw⟩, ?_⟩
  · intro S' hle hst'
    have hle' : cjSub S' ≤ S := by
      rw [← cjSub_cjSubInv S]; exact cjSub_le_iff.mpr hle
    rcases hirr _ hle' ((kStable_cjSub_iff σ S').mp hst') with h0 | h0
    · left; rw [← cjSubInv_cjSub S', h0, cjSubInv_bot]
    · right; rw [← cjSubInv_cjSub S', h0]
  · intro μ v hv hv0 hvw
    have h1 := hdom (revP μ) (Cj.mk v) hv hv0 ((isWtOn_sigC_iff σ μ v).mp hvw)
    have h2 := h n (revE ε) (revP μ) Λ h1
    rwa [dualWeight_dualWeight, revE_revE] at h2
end PI.ZuckTensorWork
