-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.projectiveLine_locDens_first_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:33:35.537889+00:00
-- url     : https://prove2.me/submissions/69fb82ab-411e-4206-ac25-4852f98a29df

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffFubiniStudyRatioCompChart0
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegralIoiFsDensRadial
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ProjectiveLinePartitionContinuousCoe
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
import Theorems.Thm_ReciprocityTheory_AnForm_maDens_fs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory OnePoint Filter Topology Set
noncomputable section
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution (y : Fin 1 → ℂ) : locDens p1 (fun _ => fsPot) p1i0 y = fsDens (y 0) := by
  apply maDens_fs
  refine Filter.Eventually.of_forall fun y' => ?_
  show fsPot.φ ((y 0 : ℂ) : OnePoint ℂ) ((y' 0 : ℂ) : OnePoint ℂ) = _
  simp only [fsPot, if_neg (coe_ne_infty _)]
  rfl
end ReciprocityTheory.AnForm.M
