-- Prove2me | solution 1 for ReciprocityTheory.AnForm.P.deriv_re_eval
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:16:47.100314+00:00
-- url     : https://prove2.me/submissions/3789fc2a-b6a6-479e-b085-e2056c55befd

import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_IsRegFamilyInhabitStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensA

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
    deriv (fun s : ℝ => (D.eval (s : ℂ)).re) = fun s : ℝ => (D.derivative.eval (s : ℂ)).re := by
  funext s
  exact ((Polynomial.hasDerivAt D (s : ℂ)).real_of_complex).deriv
end ReciprocityTheory.AnForm.P
