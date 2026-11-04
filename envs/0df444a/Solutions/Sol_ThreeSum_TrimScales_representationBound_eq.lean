-- Prove2me | solution 1 for ThreeSum.TrimScales.representationBound_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:45:27.761931+00:00
-- url     : https://prove2.me/submissions/02219c0e-c21d-4b8a-a9de-2742466642e1

import Definitions.Def_Submission_ThreeSum_Scales
import Definitions.Def_Submission_ThreeSum_LocalHashMoments
import Definitions.Def_Submission_ThreeSum_TrimScales
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
theorem _root_.solution (n : ℕ) :
    representationBound n = scheduleCount n * trimMultiplicity n := by
  simp only [representationBound, scheduleCount, replicatedHalf, trimMultiplicity, mul_pow, pow_mul]
end ThreeSum.TrimScales
