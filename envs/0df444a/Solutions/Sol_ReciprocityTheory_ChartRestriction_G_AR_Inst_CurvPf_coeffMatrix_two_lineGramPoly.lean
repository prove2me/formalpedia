-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf.coeffMatrix_two_lineGramPoly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:28:50.582849+00:00
-- url     : https://prove2.me/submissions/bd759f61-6b2b-487b-8fde-f470f26e4dff

import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_CoeffMatrixZeroCorrectedLineGramPoly
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Inst_CurvPf_coeffMatrix_zero_linearMatrixPoly
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Inst_CurvPf_coeffMatrix_one_linearMatrixPoly
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Inst_CurvPf_coeffMatrix_two_linearMatrixPoly
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Inst_CurvPf_cf_submatrix
import Theorems.Thm_ReciprocityTheory_AnForm_P_cf_mapC_mul
import Theorems.Thm_ReciprocityTheory_AnForm_P_cf_mul_two


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
open Polynomial Matrix ReciprocityTheory.AnForm.P
variable {r m : ℕ} (hm : m ≤ r) (D : Fin r → ℝ) (Y : Matrix (Fin r) (Fin r) ℂ)
namespace ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
theorem _root_.solution (t : ℂ) : cf 2 (GP hm D Y t) =
    ((starRingEnd ℂ t) * t) • (Yᴴ * Dc D * Y).submatrix (Fin.castLE hm) (Fin.castLE hm) := by
  rw [GP, cf_submatrix, cf_mul_two, cf_mapC_mul, cf_mapC_mul, cf_mapC_mul, coeffMatrix_zero_linearMatrixPoly, coeffMatrix_one_linearMatrixPoly, coeffMatrix_one_linearMatrixPoly,
    coeffMatrix_two_linearMatrixPoly, coeffMatrix_two_linearMatrixPoly, coeffMatrix_zero_linearMatrixPoly]
  simp only [Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero, one_mul, Matrix.mul_smul,
    Matrix.smul_mul, smul_smul, Matrix.mul_assoc]
  rw [mul_comm t]
  rfl
end ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
