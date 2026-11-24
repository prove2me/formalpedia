-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.existsPartition
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:19:34.455023+00:00
-- url     : https://prove2.me/submissions/125ba382-ec2d-4971-b032-fd07d67654d5

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Partition
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Theorems.Thm_ReciprocityTheory_AnForm_M_pa_holoSmooth
import Theorems.Thm_ReciprocityTheory_AnForm_exists_chart_partition


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas
open scoped ContDiff
noncomputable section
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution : ExistsPartitionStatement := by
  intro e X _ _ _ A
  obtain ⟨χ, h0, h1, h2, h3⟩ := ReciprocityTheory.AnForm.exists_chart_partition A.chart A.cover
    (fun i j => pa_holoSmooth _ _ (A.holo i j))
  exact ⟨⟨χ, fun j k => (h3 j k).mono Set.inter_subset_left, h0, h2, h1⟩⟩
end ReciprocityTheory.AnForm.M
