-- Prove2me | solution 1 for PI.Dv.TIW.intR_epsS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:56:33.546997+00:00
-- url     : https://prove2.me/submissions/44a778d6-5252-4460-927e-2e49f7de3dc0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_TauCentralScalar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_GrpNorm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_DvTransferIdxOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_MemOOfIsIntegral
import Theorems.Thm_PI_Dv_TIW_chiT_of_mem
import Theorems.Thm_PI_Dv_TIW_chiT_of_not_mem
import Theorems.Thm_PI_Dv_TIW_card_H_pos
import Theorems.Thm_PI_Dv_TIW_intR_of
import Theorems.Thm_PI_Dv_TIW_intR_zero
import Theorems.Thm_PI_Dv_TIW_intR_sum
import Theorems.Thm_PI_Dv_TIW_intR_smul
import Theorems.Thm_PI_Dv_TIW_mem_O_of_pow
import Theorems.Thm_PI_Dv_TIW_chi_inv_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.TIW
open PI.Dv NumberField
variable {K : Type} [Field K] [NumberField K] {G : Type} [Group G] [Fintype G]
namespace PI.Dv.TIW
theorem _root_.solution (P : Pair K G) : IntR (epsS P) := by
  refine intR_sum _ _ fun x _ => ?_
  by_cases hx : x ∈ P.H
  · rw [chiT_of_mem P x hx]
    exact intR_smul _ (mem_O_of_pow _ _ (card_H_pos P) (chi_inv_pow P ⟨x, hx⟩)) (intR_of x)
  · rw [chiT_of_not_mem P x hx, zero_smul]; exact intR_zero
end PI.Dv.TIW
