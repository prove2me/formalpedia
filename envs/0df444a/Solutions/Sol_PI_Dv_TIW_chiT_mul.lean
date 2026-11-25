-- Prove2me | solution 1 for PI.Dv.TIW.chiT_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:36:29.088024+00:00
-- url     : https://prove2.me/submissions/929c679e-2a6c-4419-8eb5-b06f12291c10

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_TauCentralScalar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_GrpNorm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_DvTransferIdxOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_MemOOfIsIntegral
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.TIW
open PI.Dv NumberField
variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G]
namespace PI.Dv.TIW
theorem _root_.solution (P : Pair K G) (h : P.H) (x : G) :
    chiT P x = ((P.chi h : Kˣ) : K) * chiT P ((h : G) * x) := by
  classical
  by_cases hx : x ∈ P.H
  · have hhx : (h : G) * x ∈ P.H := P.H.mul_mem h.2 hx
    simp only [chiT, dif_pos hx, dif_pos hhx]
    have : (⟨(h : G) * x, hhx⟩ : P.H) = h * ⟨x, hx⟩ := rfl
    rw [this, map_mul, mul_inv_rev, Units.val_mul, ← mul_assoc, mul_right_comm, Units.mul_inv, one_mul]
  · have hhx : (h : G) * x ∉ P.H := fun hh => hx (by simpa using P.H.mul_mem (P.H.inv_mem h.2) hh)
    simp only [chiT, dif_neg hx, dif_neg hhx, mul_zero]
end PI.Dv.TIW
