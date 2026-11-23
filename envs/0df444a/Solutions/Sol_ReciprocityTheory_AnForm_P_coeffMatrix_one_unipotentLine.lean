-- Prove2me | solution 1 for ReciprocityTheory.AnForm.P.coeffMatrix_one_unipotentLine
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:16:47.005851+00:00
-- url     : https://prove2.me/submissions/272987cc-cf19-46fe-945a-025d1aeb05a1

import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensA
import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensB
import Theorems.Thm_ReciprocityTheory_AnForm_P_cf_apply
import Theorems.Thm_ReciprocityTheory_AnForm_P_coeff_X_mul_C


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
theorem _root_.solution {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) : cf 1 (tL A) = -A := by
  ext i j
  by_cases h : i = j <;> simp [tL, cf_apply, h, Matrix.one_apply, coeff_X_mul_C, coeff_one]
end ReciprocityTheory.AnForm.P
