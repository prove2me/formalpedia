-- Prove2me | solution 1 for PI.Dv.TIW.epsS_mul_epsS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:56:07.073318+00:00
-- url     : https://prove2.me/submissions/b0ae3ee0-9dce-47cb-b7e0-1238e9475134

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_TauCentralScalar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_GrpNorm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_DvTransferIdxOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_MemOOfIsIntegral
import Theorems.Thm_PI_Dv_TIW_chiT_of_mem
import Theorems.Thm_PI_Dv_TIW_chiT_of_not_mem
import Theorems.Thm_PI_Dv_TIW_of_mul_epsS

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
theorem _root_.solution (P : Pair K G) : epsS P * epsS P = ((Nat.card P.H : ℕ) : K) • epsS P := by
  classical
  nth_rewrite 1 [epsS]
  rw [Finset.sum_mul]
  have : ∀ x : G, (chiT P x • MonoidAlgebra.of K G x) * epsS P = (if x ∈ P.H then (1 : K) else 0) • epsS P := by
    intro x
    by_cases hx : x ∈ P.H
    · rw [if_pos hx, smul_mul_assoc, of_mul_epsS P ⟨x, hx⟩, smul_smul, chiT_of_mem P x hx,
        Units.val_inv_eq_inv_val, inv_mul_cancel₀ (Units.ne_zero _)]
    · rw [if_neg hx, chiT_of_not_mem P x hx, zero_smul, zero_mul, zero_smul]
  rw [Finset.sum_congr rfl fun x _ => this x, ← Finset.sum_smul, Finset.sum_boole]
  congr 1
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
end PI.Dv.TIW
