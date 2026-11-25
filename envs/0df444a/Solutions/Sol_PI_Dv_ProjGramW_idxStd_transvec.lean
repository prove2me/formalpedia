-- Prove2me | solution 1 for PI.Dv.ProjGramW.idxStd_transvec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:21:41.300286+00:00
-- url     : https://prove2.me/submissions/bf1474b0-9e9f-44a1-8815-02b95fe59635

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionGramMatrices_AlgebraMapNeZeroOfNotMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionGramMatrices_IdxDet
import Theorems.Thm_PI_Dv_ProjGramW_idxStd_colOp
import Theorems.Thm_PI_Dv_ProjGramW_transvec_colOp
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
open PI PI.Dv PI.Dv.ProjGramW
open NumberField IsDedekindDomain Formalism.BasicNotions
variable {K : Type} [Field K] [NumberField K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace PI.Dv.ProjGramW
theorem _root_.solution (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) {d : ℕ}
    (t : Matrix.TransvectionStruct (Fin d) K) : idxStd w t.toMatrix = 0 := by
  have hdet : t.toMatrix.det ≠ 0 := by rw [Matrix.TransvectionStruct.det]; exact one_ne_zero
  have e : t.toMatrix = colOp t.j (fun p => (if p = t.j then 1 else 0) + (if p = t.i then t.c else 0)) :=
    transvec_colOp t.i t.j t.hij t.c
  rw [e] at hdet ⊢
  rw [idxStd_colOp hI w _ _ (by simp [Ne.symm t.hij]) hdet]
  simp [Ne.symm t.hij, vAdd]
end PI.Dv.ProjGramW
