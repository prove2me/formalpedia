-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.projectiveLine_partition_continuous_coe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:30:40.742648+00:00
-- url     : https://prove2.me/submissions/affece1e-6547-440c-8df5-912930f6e13d

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffFubiniStudyRatioCompChart0
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegralIoiFsDensRadial
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ProjectiveLinePartitionContinuousCoe

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
theorem _root_.solution (P : ChartPartition p1) (j : Fin p1.n) :
    Continuous fun u : ℂ => P.χ j (u : OnePoint ℂ) := by
  have h := (P.smooth j p1i0).continuousOn
  rw [show (p1.chart p1i0).target = univ from rfl, preimage_univ, inter_univ,
    continuousOn_univ] at h
  exact h.comp (continuous_pi fun _ => continuous_id)
end ReciprocityTheory.AnForm.M
