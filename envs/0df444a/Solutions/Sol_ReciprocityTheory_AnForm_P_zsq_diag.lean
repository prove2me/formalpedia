-- Prove2me | solution 1 for ReciprocityTheory.AnForm.P.zsq_diag
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:16:48.445839+00:00
-- url     : https://prove2.me/submissions/7688a877-8423-4569-9bd6-c86851cee49e

import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensA
import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensB
import Theorems.Thm_ReciprocityTheory_AnForm_P_zMat_mul_swap

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
theorem _root_.solution (N : ℕ) (z : Pairs N → ℂ) (i : Fin N) : (zMat N z ^ 2) i i = 0 := by
  rw [pow_two, Matrix.mul_apply]
  exact Finset.sum_eq_zero fun k _ => zMat_mul_swap N z i k
end ReciprocityTheory.AnForm.P
