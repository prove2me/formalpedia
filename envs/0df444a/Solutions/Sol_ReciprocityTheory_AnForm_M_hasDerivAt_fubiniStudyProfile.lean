-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.hasDerivAt_fubiniStudyProfile
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:02:32.893075+00:00
-- url     : https://prove2.me/submissions/ad689026-e0df-4583-b8c5-b5d8d8f4d4af

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialOfFun
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffOnFubiniStudyProfileInvNormSqFirst
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory OnePoint Filter Topology
noncomputable section
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution {t : ℝ} (ht : -1 < t) : HasDerivAt fubiniStudyProfile ((1 / 2) * (1 + t)⁻¹) t := by
  have h1 : HasDerivAt (fun x : ℝ => 1 + x) 1 t := (hasDerivAt_id t).const_add 1
  have h2 := (h1.log (ne_of_gt (by linarith))).const_mul (1 / 2 : ℝ)
  exact h2.congr_deriv (by simp only [one_div])
end ReciprocityTheory.AnForm.M
