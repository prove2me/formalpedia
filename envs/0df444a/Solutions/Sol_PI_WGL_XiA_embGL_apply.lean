-- Prove2me | solution 1 for PI.WGL.XiA.embGL_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:59:45.681063+00:00
-- url     : https://prove2.me/submissions/a1a18ea7-3430-4f27-9de8-bbc0aa6ad077

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_ZScalarVanish
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_MultisetProdNormLeOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_RowsZStrictMono
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
open PI PI.WGL PI.WGL.XiA
open Formalism.BasicNotions MvPolynomial
namespace PI.WGL.XiA
theorem _root_.solution {n N : ℕ} (h : n + 1 = N) (g : GL (Fin n) ℂ) (a b : Fin N) :
    ((embGL ℂ n N h g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) a b =
      if ha : a.1 < n then (if hb : b.1 < n then (g : Matrix (Fin n) (Fin n) ℂ) ⟨a.1, ha⟩ ⟨b.1, hb⟩ else 0)
      else (if b.1 < n then 0 else 1) := by
  unfold embGL blkHom
  simp [Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
  have hl : ∀ (x : Fin N) (hx : x.1 < n),
      finSumFinEquiv.symm (Fin.cast h.symm x) = (Sum.inl ⟨x.1, hx⟩ : Fin n ⊕ Fin 1) := by
    intro x hx
    have hc : Fin.cast h.symm x = Fin.castAdd 1 ⟨x.1, hx⟩ := Fin.ext rfl
    rw [hc, finSumFinEquiv_symm_apply_castAdd]
  have hr : ∀ (x : Fin N), ¬ x.1 < n →
      finSumFinEquiv.symm (Fin.cast h.symm x) = (Sum.inr 0 : Fin n ⊕ Fin 1) := by
    intro x hx
    have hxN := x.isLt
    have hc : Fin.cast h.symm x = Fin.natAdd n (0 : Fin 1) := Fin.ext (by simp; omega)
    rw [hc, finSumFinEquiv_symm_apply_natAdd]
  by_cases ha : a.1 < n <;> by_cases hb : b.1 < n
  · rw [hl a ha, hl b hb]
    simp [ha, hb]
  · rw [hl a ha, hr b hb]
    simp [ha, hb]
  · rw [hr a ha, hl b hb]
    simp [ha, hb]
  · rw [hr a ha, hr b hb]
    simp [ha, hb]
end PI.WGL.XiA
