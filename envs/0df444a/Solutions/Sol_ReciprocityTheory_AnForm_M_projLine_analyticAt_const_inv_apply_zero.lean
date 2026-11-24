-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.projLine_analyticAt_const_inv_apply_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:11:57.357303+00:00
-- url     : https://prove2.me/submissions/34d9de02-3abd-4275-a6ce-b84117aa358c

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialOfFun
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffOnFubiniStudyProfileInvNormSqFirst
import Theorems.Thm_ReciprocityTheory_AnForm_M_projLine_analyticAt_inv_apply_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory OnePoint Filter Topology
noncomputable section
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution {w : Fin 1 → ℂ} (hw : w 0 ≠ 0) :
    AnalyticAt ℂ (fun w : Fin 1 → ℂ => fun _ : Fin 1 => (w 0)⁻¹) w := AnalyticAt.pi fun _ => projLine_analyticAt_inv_apply_zero hw
end ReciprocityTheory.AnForm.M
