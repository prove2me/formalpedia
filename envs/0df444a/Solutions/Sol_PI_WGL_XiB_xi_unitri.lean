-- Prove2me | solution 1 for PI.WGL.XiB.xi_unitri
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:28:50.792346+00:00
-- url     : https://prove2.me/submissions/9fa6b9d5-fb3e-4ed8-b712-6c868bbf0893

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_RowsZStrictMono
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_EvalInitMinorNormLe
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_WGL_XiA_embGL_apply
import Theorems.Thm_PI_WGL_XiA_rowAct_xi
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
open PI PI.WGL PI.WGL.XiB
open Formalism.BasicNotions MvPolynomial
namespace PI.WGL.XiB
theorem _root_.solution {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n)
    (g : GL (Fin n) ℂ) (hlow : ∀ i j, j < i → (g : Matrix (Fin n) (Fin n) ℂ) i j = 0)
    (hdiag : ∀ i, (g : Matrix (Fin n) (Fin n) ℂ) i i = 1) :
    sqAct ℂ N lam (embGL ℂ n N h g) (xi ℂ h lam sg) = xi ℂ h lam sg := by
  set G := ((embGL ℂ n N h g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) with hGdef
  have hlowG : ∀ a b : Fin N, a < b → G b a = 0 := by
    intro a b hab
    have hab' := Fin.lt_def.mp hab
    rw [hGdef, XiA.embGL_apply]
    by_cases hb : b.1 < n
    · have ha : a.1 < n := by omega
      rw [dif_pos hb, dif_pos ha]
      exact hlow _ _ (Fin.mk_lt_mk.mpr hab')
    · have hbN := b.isLt
      rw [dif_neg hb, if_pos (by omega)]
  have hcol : ∀ b : Fin N, b.1 ≠ n → G b ⟨n, by omega⟩ = 0 := by
    intro b hb
    have hbN := b.isLt
    have hb' : b.1 < n := by omega
    rw [hGdef, XiA.embGL_apply, dif_pos hb', dif_neg (lt_irrefl n)]
  have hdg : ∀ a : Fin N, G a a = 1 := by
    intro a
    rw [hGdef, XiA.embGL_apply]
    by_cases ha : a.1 < n
    · rw [dif_pos ha, dif_pos ha]
      exact hdiag ⟨a.1, ha⟩
    · rw [dif_neg ha, if_neg ha]
  have hgood : XiA.GoodG n h G := by
    unfold XiA.GoodG
    exact ⟨hlowG, hcol⟩
  have hdet : G.det = 1 := by
    rw [Matrix.det_of_upperTriangular (fun i j hij => hlowG j i hij)]
    simp [hdg]
  have hxs : XiA.xiScal h lam sg G = 1 := by
    unfold XiA.xiScal
    simp [hdg]
  unfold sqAct
  rw [XiA.rowAct_xi h lam sg G hgood, hxs, MvPolynomial.C_1, one_mul]
  have hdu : Matrix.GeneralLinearGroup.det (embGL ℂ n N h g) = 1 := by
    apply Units.ext
    rw [Units.val_one, Matrix.GeneralLinearGroup.val_det_apply, ← hGdef, hdet]
  unfold detPow
  rw [hdu]
  simp
end PI.WGL.XiB
