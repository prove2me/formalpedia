-- Prove2me | solution 1 for ReciprocityTheory.AnForm.P.coeffMatrix_two_gramPoly_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:26:27.767779+00:00
-- url     : https://prove2.me/submissions/46cf6859-9cec-4e1d-9ca7-9b5257541bdb

import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensA
import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensB
import Theorems.Thm_ReciprocityTheory_AnForm_P_cf_mul_two
import Theorems.Thm_ReciprocityTheory_AnForm_P_zMat_of_le_one
import Theorems.Thm_ReciprocityTheory_AnForm_P_zsq_diag
import Theorems.Thm_ReciprocityTheory_AnForm_P_zhsq_diag
import Theorems.Thm_ReciprocityTheory_AnForm_P_coeffMatrix_zero_truncExpPoly
import Theorems.Thm_ReciprocityTheory_AnForm_P_coeffMatrix_one_truncExpPoly
import Theorems.Thm_ReciprocityTheory_AnForm_P_coeffMatrix_two_truncExpPoly
import Theorems.Thm_ReciprocityTheory_AnForm_P_cf_mapC_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.P
open Polynomial Matrix
noncomputable section
namespace ReciprocityTheory.AnForm.P
theorem _root_.solution (N : ℕ) (hd : Fin N → ℝ) (v : Pairs N → ℂ) (i : Fin N) :
    cf 2 (gP N hd v) i i = ∑ k, star (zMat N v k i) * ((hd k : ℂ) * zMat N v k i) := by
  have h1 := coeffMatrix_one_truncExpPoly N (zMat N v) (fun h => zMat_of_le_one v h)
  have h2 := coeffMatrix_one_truncExpPoly N (zMat N v)ᴴ (fun h => by rw [zMat_of_le_one v h, conjTranspose_zero])
  obtain ⟨c1, e1⟩ := coeffMatrix_two_truncExpPoly N (zMat N v)
  obtain ⟨c2, e2⟩ := coeffMatrix_two_truncExpPoly N (zMat N v)ᴴ
  rw [gP, cf_mul_two, cf_mapC_mul, cf_mapC_mul, cf_mapC_mul, coeffMatrix_zero_truncExpPoly, coeffMatrix_zero_truncExpPoly, h1, h2, e1, e2]
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.add_apply, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.smul_apply, smul_eq_mul, Matrix.diagonal_mul, Matrix.mul_diagonal, zsq_diag, zhsq_diag,
    mul_zero, zero_mul, zero_add, add_zero]
  rw [Matrix.mul_apply]
  simp only [Matrix.diagonal_mul, conjTranspose_apply]
end ReciprocityTheory.AnForm.P
