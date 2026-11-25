-- Prove2me | solution 1 for PI.Dv.ProjGramW.idxStd_list
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:28:00.879861+00:00
-- url     : https://prove2.me/submissions/3ef1af1e-efb9-4972-a1b9-419fee226d51

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionGramMatrices_AlgebraMapNeZeroOfNotMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionGramMatrices_IdxDet
import Theorems.Thm_PI_Dv_ProjGramW_idxStd_mul
import Theorems.Thm_PI_Dv_ProjGramW_idxStd_one
import Theorems.Thm_PI_Dv_ProjGramW_idxStd_transvec
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
    (L : List (Matrix.TransvectionStruct (Fin d) K)) :
    idxStd w (L.map Matrix.TransvectionStruct.toMatrix).prod = 0 := by
  induction L with
  | nil => simpa using idxStd_one hI w d
  | cons t L ih =>
    rw [List.map_cons, List.prod_cons]
    have h1 : t.toMatrix.det ≠ 0 := by rw [Matrix.TransvectionStruct.det]; exact one_ne_zero
    have h2 : (L.map Matrix.TransvectionStruct.toMatrix).prod.det ≠ 0 := by
      rw [Matrix.TransvectionStruct.det_toMatrix_prod]; exact one_ne_zero
    rw [idxStd_mul hI w _ _ h1 h2, ih, idxStd_transvec hI w t, add_zero]
end PI.Dv.ProjGramW
