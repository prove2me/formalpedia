-- Prove2me | solution 1 for ReciprocityTheory.AnForm.P.fderiv_line_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:19:31.296859+00:00
-- url     : https://prove2.me/submissions/92fe36da-6da5-4146-999d-0852b1f1b007

import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_IsRegFamilyInhabitStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensA
import Theorems.Thm_ReciprocityTheory_AnForm_P_hasDerivAt_line

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
    (hφ : DifferentiableAt ℝ φ 0) (v : E) :
    fderiv ℝ φ 0 v = deriv (fun s : ℝ => φ (s • v)) 0 := by
  have h := hasDerivAt_line (v := v) (t := 0) (by rwa [zero_smul])
  rw [h.deriv, zero_smul]
end ReciprocityTheory.AnForm.P
