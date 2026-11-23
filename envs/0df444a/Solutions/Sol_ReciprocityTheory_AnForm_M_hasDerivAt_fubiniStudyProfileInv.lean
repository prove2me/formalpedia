-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.hasDerivAt_fubiniStudyProfileInv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:02:33.354971+00:00
-- url     : https://prove2.me/submissions/7c870f0e-62b2-4437-9a6f-f9b5ac0dcb6a

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
theorem _root_.solution {t : ℝ} (ht : 0 < t) :
    HasDerivAt fubiniStudyProfileInv (-(1 / 2) * (t * (t + 1))⁻¹) t := by
  have ht0 : t ≠ 0 := ht.ne'
  have ht1 : t + 1 ≠ 0 := by positivity
  have h1 : HasDerivAt (fun x : ℝ => 1 + x⁻¹) (-(t ^ 2)⁻¹) t := (hasDerivAt_inv ht0).const_add 1
  have hne : 1 + t⁻¹ ≠ 0 := by positivity
  have h2 := (h1.log hne).const_mul (1 / 2 : ℝ)
  refine h2.congr_deriv ?_
  field_simp
end ReciprocityTheory.AnForm.M
