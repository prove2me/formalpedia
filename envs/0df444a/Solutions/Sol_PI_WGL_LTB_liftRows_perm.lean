-- Prove2me | solution 1 for PI.WGL.LTB.liftRows_perm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:09:09.388809+00:00
-- url     : https://prove2.me/submissions/7a5a5173-9f4f-42c3-9aad-820950053827

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleM
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleB
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.WGL PI.WGL.LTB
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial PI.WGL.LTM
namespace PI.WGL.LTB
theorem _root_.solution {n N : ℕ} (h : n + 1 = N) {m : ℕ} (ρ : Fin m → Fin n) (σ : Equiv.Perm (Fin m)) :
    liftRows h (ρ ∘ σ) = liftRows h ρ ∘ (σ.viaFintypeEmbedding Fin.castSuccEmb) := by
  funext p
  induction p using Fin.lastCases with
  | last =>
    have hnot : Fin.last m ∉ Set.range (Fin.castSuccEmb : Fin m ↪ Fin (m + 1)) := by
      rintro ⟨y, hy⟩
      have h1 : y.val = m := by
        have := congrArg Fin.val hy
        exact this
      have h2 := y.2
      omega
    rw [Function.comp_apply]
    first
    | rw [Equiv.Perm.viaFintypeEmbedding_apply_notMem_range _ _ hnot]
    | rw [Equiv.Perm.viaFintypeEmbedding_apply_not_mem_range _ _ hnot]
    | rw [Equiv.Perm.viaFintypeEmbedding_apply_notMem_range hnot]
    | rw [Equiv.Perm.viaFintypeEmbedding_apply_not_mem_range hnot]
    simp [liftRows]
  | cast i =>
    rw [Function.comp_apply]
    have e := Equiv.Perm.viaFintypeEmbedding_apply_image σ (Fin.castSuccEmb : Fin m ↪ Fin (m + 1)) i
    rw [show Fin.castSucc i = (Fin.castSuccEmb : Fin m ↪ Fin (m + 1)) i from rfl, e]
    simp [liftRows]
end PI.WGL.LTB
