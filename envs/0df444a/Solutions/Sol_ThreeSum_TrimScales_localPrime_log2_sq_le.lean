-- Prove2me | solution 1 for ThreeSum.TrimScales.localPrime_log2_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:18:15.392896+00:00
-- url     : https://prove2.me/submissions/eada29c9-f9d3-4bcd-bebc-8bc4b88d424c

import Definitions.Def_Submission_ThreeSum_Scales
import Definitions.Def_Submission_ThreeSum_LocalHashMoments
import Definitions.Def_Submission_ThreeSum_TrimScales
import Definitions.Def_WeightedCache3SUM_Alias_b63fb9a403cfdb9c
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
theorem _root_.solution (h : ℕ) :
    Nat.log2 (LocalCoverBounds.localPrime h ^ 2) ≤ 4 + 514 * h := by
  rw [Nat.log2_eq_log_two]
  have hm := Nat.log_mono_right (b := 2) (localPrime_sq_le_power h)
  simpa only [Nat.log_pow (by decide : 1 < 2)] using hm
end ThreeSum.TrimScales
