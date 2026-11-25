-- Prove2me | solution 1 for PI.WGL.EqvWt.embGL_diagGL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:07:11.832263+00:00
-- url     : https://prove2.me/submissions/2635cff7-42e3-4e2a-9c5e-57c73a7909ec

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftEqvWt
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
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
open PI.WGL.EqvWt
namespace PI.WGL.EqvWt
theorem _root_.solution {n : ℕ} (t : Fin n → ℂˣ) :
    embGL ℂ n (n + 1) rfl (diagGL ℂ n t) =
      diagGL ℂ (n + 1) (fun a => if ha : a.1 < n then t ⟨a.1, ha⟩ else 1) := by
  apply Units.ext
  ext i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp [embGL, blkHom, diagGL, Matrix.diagonal_apply, Matrix.reindexAlgEquiv_apply,
      Matrix.reindex_apply, Matrix.submatrix_apply, Fin.ext_iff] <;> omega
end PI.WGL.EqvWt
