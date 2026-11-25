-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.projectiveLine_fubiniStudy_mass_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:08:57.077662+00:00
-- url     : https://prove2.me/submissions/8e37327d-ea8d-4c3e-95f4-eacd0092ee85

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffFubiniStudyRatioCompChart0
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegralIoiFsDensRadial
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ProjectiveLinePartitionContinuousCoe
import Theorems.Thm_ReciprocityTheory_AnForm_M_projectiveLine_integralWith_eq_one
import Theorems.Thm_ReciprocityTheory_AnForm_M_projLine_partition


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory OnePoint Filter Topology Set
noncomputable section
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution : mInt p1 (fun _ => fsPot) (fun _ => 1) = 1 := by
  rw [mInt, dif_pos projLine_partition]
  exact projectiveLine_integralWith_eq_one _
end ReciprocityTheory.AnForm.M
