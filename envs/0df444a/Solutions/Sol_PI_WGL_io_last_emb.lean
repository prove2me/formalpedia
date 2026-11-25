-- Prove2me | solution 1 for PI.WGL.io_last_emb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:09:07.608311+00:00
-- url     : https://prove2.me/submissions/cc0ba0de-4447-4e62-8d2a-a20c69f83c66

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_ZScalarVanish
import Definitions.Def_Formalism_PeriodIntegrals_HwIrred
import Definitions.Def_Formalism_PeriodIntegrals_GTBranch
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_IoExistsOfCap
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
open PI PI.WGL
open Formalism.BasicNotions MvPolynomial
namespace PI.WGL
theorem _root_.solution {n N : ℕ} (h : n + 1 = N) (a : ℂˣ) (g : GL (Fin n) ℂ) :
    lastGL ℂ N a * embGL ℂ n N h g = embGL ℂ n N h g * lastGL ℂ N a := by
  have hL : ((lastGL ℂ N a : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) =
      Matrix.diagonal (fun x : Fin N => ((if x.1 + 1 = N then a else 1 : ℂˣ) : ℂ)) := rfl
  have hE : ((embGL ℂ n N h g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) =
      (Matrix.fromBlocks (g : Matrix (Fin n) (Fin n) ℂ) 0 0 1).submatrix
        (finSumFinEquiv.trans (finCongr h)).symm (finSumFinEquiv.trans (finCongr h)).symm := rfl
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hL, hE]
  ext i j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  obtain ⟨s, rfl⟩ := (finSumFinEquiv.trans (finCongr h)).surjective i
  obtain ⟨t, rfl⟩ := (finSumFinEquiv.trans (finCongr h)).surjective j
  simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rcases s with k | k <;> rcases t with l | l
  · have hk : ¬ ((((finSumFinEquiv.trans (finCongr h)) (Sum.inl k) : Fin N) : ℕ) + 1 = N) := by
      have := k.isLt
      simp only [Equiv.trans_apply, finSumFinEquiv_apply_left, finCongr_apply, Fin.coe_cast,
        Fin.coe_castAdd]
      omega
    have hl : ¬ ((((finSumFinEquiv.trans (finCongr h)) (Sum.inl l) : Fin N) : ℕ) + 1 = N) := by
      have := l.isLt
      simp only [Equiv.trans_apply, finSumFinEquiv_apply_left, finCongr_apply, Fin.coe_cast,
        Fin.coe_castAdd]
      omega
    rw [if_neg hk, if_neg hl]
    simp
  · simp
  · simp
  · obtain rfl : k = l := Subsingleton.elim _ _
    exact mul_comm _ _
end PI.WGL
