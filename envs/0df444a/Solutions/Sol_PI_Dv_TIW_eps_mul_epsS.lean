-- Prove2me | solution 1 for PI.Dv.TIW.eps_mul_epsS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:03:46.771596+00:00
-- url     : https://prove2.me/submissions/e7fa9c49-2234-4fd7-aa5f-19bfd46a8753

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_TauCentralScalar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_GrpNorm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_DvTransferIdxOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_MemOOfIsIntegral
import Theorems.Thm_PI_Dv_TIW_eps_eq
import Theorems.Thm_PI_Dv_TIW_card_H_pos
import Theorems.Thm_PI_Dv_TIW_epsS_mul_epsS

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
variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G]
namespace PI.Dv.TIW
theorem _root_.solution (P : Pair K G) : eps P * epsS P = epsS P := by
  rw [eps_eq, smul_mul_assoc, epsS_mul_epsS, smul_smul]
  have : ((Nat.card P.H : ℕ) : K) ≠ 0 := by exact_mod_cast (card_H_pos P).ne'
  rw [inv_mul_cancel₀ this, one_smul]
end PI.Dv.TIW
