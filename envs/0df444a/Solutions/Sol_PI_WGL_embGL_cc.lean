-- Prove2me | solution 1 for PI.WGL.embGL_cc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:12:12.90333+00:00
-- url     : https://prove2.me/submissions/9396caea-f2a3-4abd-8578-3b75e456782c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_CapelliOps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightIrreducible_ConstructionA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_CapelliEqv
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
namespace PI.WGL
theorem _root_.solution {n : ℕ} (g : GL (Fin n) ℂ) (i j : Fin n) :
    (embGL ℂ n (n + 1) rfl g : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (Fin.castSucc i) (Fin.castSucc j) = g i j := by
  simp [embGL, blkHom, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, Matrix.submatrix_apply]
end PI.WGL
