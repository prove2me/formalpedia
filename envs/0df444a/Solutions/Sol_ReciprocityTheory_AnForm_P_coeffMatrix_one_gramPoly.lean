-- Prove2me | solution 1 for ReciprocityTheory.AnForm.P.coeffMatrix_one_gramPoly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:33:43.626443+00:00
-- url     : https://prove2.me/submissions/c5c6fd24-5ab4-4ef0-87ea-50e2e1c1b1ec

import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensA
import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensB
import Theorems.Thm_ReciprocityTheory_AnForm_P_cf_mul_one
import Theorems.Thm_ReciprocityTheory_AnForm_P_zMat_of_le_one
import Theorems.Thm_ReciprocityTheory_AnForm_P_coeffMatrix_zero_truncExpPoly
import Theorems.Thm_ReciprocityTheory_AnForm_P_coeffMatrix_one_truncExpPoly
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
theorem _root_.solution (N : ℕ) (hd : Fin N → ℝ) (v : Pairs N → ℂ) :
    cf 1 (gP N hd v) = (diagonal fun k => (hd k : ℂ)) * zMat N v +
      (zMat N v)ᴴ * diagonal fun k => (hd k : ℂ) := by
  have h1 := coeffMatrix_one_truncExpPoly N (zMat N v) (fun h => zMat_of_le_one v h)
  have h2 := coeffMatrix_one_truncExpPoly N (zMat N v)ᴴ (fun h => by rw [zMat_of_le_one v h, conjTranspose_zero])
  rw [gP, cf_mul_one, cf_mapC_mul, cf_mapC_mul, coeffMatrix_zero_truncExpPoly, coeffMatrix_zero_truncExpPoly, h1, h2, Matrix.one_mul,
    Matrix.mul_one]
end ReciprocityTheory.AnForm.P
