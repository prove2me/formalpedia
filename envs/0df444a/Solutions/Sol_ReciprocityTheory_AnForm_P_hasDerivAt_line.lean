-- Prove2me | solution 1 for ReciprocityTheory.AnForm.P.hasDerivAt_line
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:16:47.542797+00:00
-- url     : https://prove2.me/submissions/bff0840e-84d2-4dd4-ad32-a0356f834d1b

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
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {φ : E → ℝ}
    {v : E} {t : ℝ} (h : DifferentiableAt ℝ φ (t • v)) :
    HasDerivAt (fun s : ℝ => φ (s • v)) (fderiv ℝ φ (t • v) v) t := by
  have h1 : HasDerivAt (fun s : ℝ => s • v) v t := by simpa using (hasDerivAt_id t).smul_const v
  exact h.hasFDerivAt.comp_hasDerivAt t h1
end ReciprocityTheory.AnForm.P
