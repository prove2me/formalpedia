-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.contDiff_fsQ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:42:44.654791+00:00
-- url     : https://prove2.me/submissions/cba4b49e-2440-4829-be05-c0499d63fa9b

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialOfFun
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffOnFubiniStudyProfileInvNormSqFirst

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
theorem _root_.solution : ContDiff ℝ (⊤ : ℕ∞) fsQ := (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ ℂ 0)
end ReciprocityTheory.AnForm.M
