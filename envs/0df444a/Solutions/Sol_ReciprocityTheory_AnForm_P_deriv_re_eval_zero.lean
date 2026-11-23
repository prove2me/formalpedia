-- Prove2me | solution 1 for ReciprocityTheory.AnForm.P.deriv_re_eval_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:18:55.602805+00:00
-- url     : https://prove2.me/submissions/ca11e252-5355-4c1c-b793-3f4570cc91c8

import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_IsRegFamilyInhabitStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensA
import Theorems.Thm_ReciprocityTheory_AnForm_P_deriv_re_eval

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.P
open Filter Topology Polynomial Matrix
open scoped ContDiff
noncomputable section
namespace ReciprocityTheory.AnForm.P
theorem _root_.solution (D : ℂ[X]) :
    deriv (fun s : ℝ => (D.eval (s : ℂ)).re) 0 = (D.coeff 1).re := by
  rw [deriv_re_eval]
  simp [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative]
end ReciprocityTheory.AnForm.P
