-- Prove2me | solution 1 for PI.Dv.Tr.card_S_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:30:01.79555+00:00
-- url     : https://prove2.me/submissions/2dd8cb26-adcc-42cb-9eba-125c15bf348a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_HarderNarasimhan_FinalCor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_TraceFormulaOfRankDegree
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_ESMulESOfNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_CharacteristicPolynomialCompatibility
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_NormAtAddLe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_DegGeOfInj
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_FgOfLeL
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_DegTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_TraceFiniteOrder
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_RankIdentity
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_Dv_Tr_eS_idem
import Theorems.Thm_PI_Dv_Tr_eS_ne_zero
import Theorems.Thm_PI_Dv_Tr_eS_orth
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
open PI PI.Dv PI.Dv.Tr
open PI.Dv Module NumberField
variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G]
namespace PI.Dv.Tr
theorem _root_.solution (T : GoodSet K G) : Fintype.card T.S ≤ Fintype.card G := by
  classical
  set U := Submodule.span K (Set.range (MonoidAlgebra.of K G)) with hU
  have hmem : ∀ s, eS T s ∈ U := fun s =>
    U.sum_mem fun y _ => U.smul_mem _ (Submodule.subset_span ⟨y, rfl⟩)
  let v : T.S → U := fun s => ⟨eS T s, hmem s⟩
  have hli : LinearIndependent K (fun s => eS T s) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc t
    have h1 := congrArg (fun x => x * eS T t) hc
    simp only [Finset.sum_mul, smul_mul_assoc, zero_mul] at h1
    rw [Finset.sum_eq_single t] at h1
    · rw [eS_idem] at h1
      rcases smul_eq_zero.mp h1 with h | h
      · exact h
      · exact absurd h (eS_ne_zero T t)
    · intro s _ hs; rw [eS_orth T s t hs, smul_zero]
    · simp
  have hv : LinearIndependent K v := LinearIndependent.of_comp U.subtype hli
  have h1 := hv.fintype_card_le_finrank
  have h2 : finrank K U ≤ Fintype.card G := finrank_range_le_card _
  omega
end PI.Dv.Tr
