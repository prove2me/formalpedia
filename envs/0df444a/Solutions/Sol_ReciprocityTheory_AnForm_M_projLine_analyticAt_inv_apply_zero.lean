-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.projLine_analyticAt_inv_apply_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:18:36.224692+00:00
-- url     : https://prove2.me/submissions/b57ee5a9-7136-4cb3-9cb3-0a4827b9eaf7

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialOfFun
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffOnFubiniStudyProfileInvNormSqFirst
import Theorems.Thm_ReciprocityTheory_AnForm_M_projLine_analyticAt_apply_zero

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
    AnalyticAt ℂ (fun w : Fin 1 → ℂ => (w 0)⁻¹) w := (projLine_analyticAt_apply_zero w).inv hw
end ReciprocityTheory.AnForm.M
