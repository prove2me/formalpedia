-- Prove2me | solution 1 for ThreeSum.TrimScales.scheduleCount_log_rate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:29:31.586029+00:00
-- url     : https://prove2.me/submissions/eb09996b-7114-4ff6-adfa-b7916d636fe0

import Definitions.Def_Submission_ThreeSum_Scales
import Definitions.Def_Submission_ThreeSum_LocalHashMoments
import Definitions.Def_Submission_ThreeSum_TrimScales
import Definitions.Def_WeightedCache3SUM_Alias_8c840be79f696836
import Definitions.Def_WeightedCache3SUM_Alias_f6fd57630076b427
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices



set_option autoImplicit false
open ThreeSum ThreeSum.TrimScales
open Filter Real ThreeSum.Scales
open scoped Topology
noncomputable section
namespace ThreeSum.TrimScales
theorem _root_.solution :
    Tendsto (fun n : ℕ => Real.log (scheduleCount n : ℝ) / Real.log n) atTop (𝓝 0) := by
  simpa [scheduleCount] using replicatedHalf_log_rate localLength_log_rate
end ThreeSum.TrimScales
