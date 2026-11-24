-- Prove2me | solution 1 for PI.WGB.embGL_diag_B
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:04:46.252713+00:00
-- url     : https://prove2.me/submissions/5ab60966-f195-41c3-bafc-caea8e226863

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_FockFEqSumOfSubsetB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_RowActDiagMonomial
import Theorems.Thm_PI_WGB_embGL_apply_B
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
theorem _root_.solution {n N : ℕ} (h : n + 1 = N) (t : Fin n → ℂˣ) :
    ((embGL ℂ n N h (diagGL ℂ n t) : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) =
      Matrix.diagonal (dB n N (fun j => (t j : ℂ))) := by
  ext a b
  have ha2 := a.2
  have hb2 := b.2
  rw [embGL_apply_B, Matrix.diagonal_apply]
  by_cases ha : a.1 < n <;> by_cases hb : b.1 < n
  · rw [dif_pos ha, dif_pos hb]
    show (Matrix.diagonal fun a => (t a : ℂ)) ⟨a.1, ha⟩ ⟨b.1, hb⟩ = _
    rw [Matrix.diagonal_apply]
    by_cases hab : a = b
    · subst hab
      simp [dB, ha]
    · have hne : (⟨a.1, ha⟩ : Fin n) ≠ ⟨b.1, hb⟩ := fun e => hab (Fin.ext (Fin.mk.inj_iff.mp e))
      simp [hab, hne]
  · have hab : a ≠ b := fun e => hb (e ▸ ha)
    rw [dif_pos ha, dif_neg hb, if_neg hab]
  · have hab : a ≠ b := fun e => ha (e ▸ hb)
    rw [dif_neg ha, if_pos hb, if_neg hab]
  · have hab : a = b := Fin.ext (by omega)
    subst hab
    rw [dif_neg ha, if_neg hb, if_pos rfl]
    simp [dB, ha]
end PI.WGB
