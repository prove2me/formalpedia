-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf.coeffMatrix_two_correctedLineGramPoly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:03:19.985735+00:00
-- url     : https://prove2.me/submissions/84f983c8-f095-4275-a754-0244ff26f1e9

import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_CoeffMatrixZeroCorrectedLineGramPoly
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Inst_CurvPf_coeffMatrix_zero_linearMatrixPoly
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Inst_CurvPf_coeffMatrix_one_linearMatrixPoly
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Inst_CurvPf_coeffMatrix_two_linearMatrixPoly
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Inst_CurvPf_coeffMatrix_zero_lineGramPoly
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Inst_CurvPf_coeffMatrix_one_lineGramPoly
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Inst_CurvPf_coeffMatrix_two_lineGramPoly
import Theorems.Thm_ReciprocityTheory_AnForm_P_cf_mul_one
import Theorems.Thm_ReciprocityTheory_AnForm_P_cf_mul_two
import Theorems.Thm_ReciprocityTheory_AnForm_P_cf_mul_zero


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
theorem _root_.solution (t : ℂ) : cf 2 (GnP hm D Y t) =
    ((starRingEnd ℂ t) * t) • ((Yᴴ * Dc D * Y).submatrix (Fin.castLE hm) (Fin.castLE hm) -
      (Ym hm Y)ᴴ * Dm hm D * Ym hm Y) - t ^ 2 • (Dm hm D * Ym hm Y * Ym hm Y) -
      (starRingEnd ℂ t) ^ 2 • ((Ym hm Y)ᴴ * (Ym hm Y)ᴴ * Dm hm D) := by
  rw [GnP, cf_mul_two, cf_mul_two, cf_mul_one, cf_mul_zero, coeffMatrix_zero_linearMatrixPoly, coeffMatrix_one_linearMatrixPoly, coeffMatrix_two_linearMatrixPoly, coeffMatrix_zero_linearMatrixPoly, coeffMatrix_one_linearMatrixPoly,
    coeffMatrix_two_linearMatrixPoly, coeffMatrix_zero_lineGramPoly, coeffMatrix_one_lineGramPoly, coeffMatrix_two_lineGramPoly]
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.add_mul, Matrix.mul_add,
    Matrix.mul_assoc, smul_smul]
  module
end ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
