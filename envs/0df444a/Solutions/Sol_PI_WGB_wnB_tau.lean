-- Prove2me | solution 1 for PI.WGB.wnB_tau
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:07:31.297828+00:00
-- url     : https://prove2.me/submissions/206b0dcf-ce97-4c3b-be39-cfa87c43efdb

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_DetPowUnitriB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_RenameTauHomogB
import Theorems.Thm_PI_WGB_tauB_val
import Theorems.Thm_PI_WGB_tauB_of_not
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
open PI PI.WGB
open Formalism.BasicNotions MvPolynomial
namespace PI.WGB
theorem _root_.solution {n N : ℕ} (h : n + 1 = N) (σ : Equiv.Perm (Fin n)) (hσ : ∀ j, σ (σ j) = j)
    (v : Fin N × Fin N) : wnB n N (tauB h σ v.1, v.2) = fun j => wnB n N v (σ j) := by
  funext j
  by_cases ha : v.1.1 < n
  · have h2 : (tauB h σ v.1).1 < n := by rw [tauB_val h σ _ ha]; exact (σ _).isLt
    dsimp only [wnB]
    rw [dif_pos h2, dif_pos ha]
    have e : (⟨(tauB h σ v.1).1, h2⟩ : Fin n) = σ ⟨v.1.1, ha⟩ := Fin.ext (tauB_val h σ _ ha)
    rw [e, Pi.single_apply, Pi.single_apply]
    by_cases hj : σ j = ⟨v.1.1, ha⟩
    · rw [if_pos hj, if_pos (by rw [← hj, hσ])]
    · rw [if_neg hj, if_neg (fun e => hj (by rw [e, hσ]))]
  · have h2 : ¬ (tauB h σ v.1).1 < n := by rw [tauB_of_not h σ _ ha]; exact ha
    dsimp only [wnB]
    rw [dif_neg h2, dif_neg ha]
    rfl
end PI.WGB
