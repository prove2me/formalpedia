-- Prove2me | solution 1 for PI.Dv.ProjGramW.idxStd_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:35:47.942522+00:00
-- url     : https://prove2.me/submissions/4d5fdeb8-1205-4b82-b38a-6d9e8c9a2d5a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionGramMatrices_AlgebraMapNeZeroOfNotMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionGramMatrices_IdxDet
import Theorems.Thm_PI_Dv_ProjGramW_idxStd_mul
import Theorems.Thm_PI_Dv_ProjGramW_idxStd_diag
import Theorems.Thm_PI_Dv_ProjGramW_idxStd_list

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.ProjGramW
open NumberField IsDedekindDomain Formalism.BasicNotions
variable {K : Type} [Field K] [NumberField K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace PI.Dv.ProjGramW
theorem _root_.solution (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) {d : ℕ} (C : Matrix (Fin d) (Fin d) K)
    (hC : C.det ≠ 0) : idxStd w C = vAdd w C.det := by
  classical
  obtain ⟨L, L', D, hCe⟩ := Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec C
  have hdL := Matrix.TransvectionStruct.det_toMatrix_prod L
  have hdL' := Matrix.TransvectionStruct.det_toMatrix_prod L'
  have hdetC : C.det = ∏ k, D k := by
    rw [hCe, Matrix.det_mul, Matrix.det_mul, hdL, hdL', Matrix.det_diagonal]
    ring
  have hD : ∀ k, D k ≠ 0 := fun k => Finset.prod_ne_zero_iff.mp (hdetC ▸ hC) k (Finset.mem_univ _)
  have hdD : (Matrix.diagonal D).det ≠ 0 := by rw [Matrix.det_diagonal, ← hdetC]; exact hC
  have h1 : (L.map Matrix.TransvectionStruct.toMatrix).prod.det ≠ 0 := by rw [hdL]; exact one_ne_zero
  have h1' : (L'.map Matrix.TransvectionStruct.toMatrix).prod.det ≠ 0 := by rw [hdL']; exact one_ne_zero
  have h12 : ((L.map Matrix.TransvectionStruct.toMatrix).prod * Matrix.diagonal D).det ≠ 0 := by
    rw [Matrix.det_mul]; exact mul_ne_zero h1 hdD
  rw [hdetC, hCe, idxStd_mul hI w _ _ h12 h1', idxStd_mul hI w _ _ h1 hdD, idxStd_list hI w L,
    idxStd_list hI w L', idxStd_diag hI w D hD]
  ring
end PI.Dv.ProjGramW
