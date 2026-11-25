-- Prove2me | solution 1 for PI.Dv.TIW.eS_mul_eS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:19:03.672089+00:00
-- url     : https://prove2.me/submissions/fb33f937-fa40-4c5d-990c-a2548debb08f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_TauCentralScalar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_GrpNorm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_DvTransferIdxOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_MemOOfIsIntegral
import Theorems.Thm_PI_Dv_TIW_eS_orth
import Theorems.Thm_PI_Dv_TIW_eS_idem


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
variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G] (T : GoodSet K G)
namespace PI.Dv.TIW
theorem _root_.solution (s t : T.S) : eS T s * eS T t = if s = t then eS T s else 0 := by
  split_ifs with h
  · subst h; exact eS_idem T s
  · exact eS_orth T s t h
end PI.Dv.TIW
