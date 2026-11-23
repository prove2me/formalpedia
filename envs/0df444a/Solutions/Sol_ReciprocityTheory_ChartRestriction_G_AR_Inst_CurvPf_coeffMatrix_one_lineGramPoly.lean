-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf.coeffMatrix_one_lineGramPoly
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:18:37.671777+00:00
-- url     : https://prove2.me/submissions/7d034859-088e-45ce-8ae7-6d49a4f88abd

import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_CoeffMatrixZeroCorrectedLineGramPoly
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Inst_CurvPf_coeffMatrix_zero_linearMatrixPoly
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Inst_CurvPf_coeffMatrix_one_linearMatrixPoly
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Inst_CurvPf_cf_submatrix
import Theorems.Thm_ReciprocityTheory_AnForm_P_cf_mapC_mul
import Theorems.Thm_ReciprocityTheory_AnForm_P_cf_mul_one


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
theorem _root_.solution (t : ℂ) : cf 1 (GP hm D Y t) =
    (starRingEnd ℂ t) • ((Ym hm Y)ᴴ * Dm hm D) + t • (Dm hm D * Ym hm Y) := by
  rw [GP, cf_submatrix, cf_mul_one, cf_mapC_mul, cf_mapC_mul, coeffMatrix_zero_linearMatrixPoly, coeffMatrix_one_linearMatrixPoly, coeffMatrix_one_linearMatrixPoly, coeffMatrix_zero_linearMatrixPoly,
    one_mul, mul_one]
  ext i j
  simp [Dc, Dm, Ym, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.conjTranspose_apply]
  ring
end ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
