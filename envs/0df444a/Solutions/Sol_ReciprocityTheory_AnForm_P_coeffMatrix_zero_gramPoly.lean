-- Prove2me | solution 1 for ReciprocityTheory.AnForm.P.coeffMatrix_zero_gramPoly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:26:31.163693+00:00
-- url     : https://prove2.me/submissions/00da6478-6d3b-46f7-abee-98e31f2e916c

import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensA
import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensB
import Theorems.Thm_ReciprocityTheory_AnForm_P_cf_mul_zero
import Theorems.Thm_ReciprocityTheory_AnForm_P_coeffMatrix_zero_truncExpPoly
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
    cf 0 (gP N hd v) = diagonal fun k => (hd k : ℂ) := by
  rw [gP, cf_mul_zero, cf_mapC_mul, coeffMatrix_zero_truncExpPoly, coeffMatrix_zero_truncExpPoly, Matrix.one_mul, Matrix.mul_one]
end ReciprocityTheory.AnForm.P
