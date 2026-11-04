-- Prove2me | solution 1 for ThreeSum.TrimScales.localBucketCap_ge_load
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:17:11.392578+00:00
-- url     : https://prove2.me/submissions/4d3c23df-83a0-4e2f-a15a-2c999380c6ac

import Definitions.Def_Submission_ThreeSum_Scales
import Definitions.Def_Submission_ThreeSum_LocalHashMoments
import Definitions.Def_Submission_ThreeSum_TrimScales
import Theorems.Thm_ThreeSum_LocalCoverBounds_localBucketCap_threshold
import Theorems.Thm_ThreeSum_LocalCoverBounds_localPrime_pos


set_option autoImplicit false
open ThreeSum ThreeSum.TrimScales
open Filter Real ThreeSum.Scales
open scoped Topology
noncomputable section
namespace ThreeSum.TrimScales
theorem _root_.solution (h : ℕ) :
    vertexLoad h ≤ (LocalCoverBounds.localBucketCap h : ℝ) := by
  have hp : (0 : ℝ) < LocalCoverBounds.localPrime h := by
    exact_mod_cast LocalCoverBounds.localPrime_pos h
  have hV : (0 : ℝ) ≤ LocalCoverBounds.vertexCount (512 * h) h := Nat.cast_nonneg _
  have ht : 4 * (LocalCoverBounds.localPrime h +
      (LocalCoverBounds.vertexCount (512 * h) h : ℝ)) ≤
      (LocalCoverBounds.localBucketCap h : ℝ) * LocalCoverBounds.localPrime h := by
    exact_mod_cast LocalCoverBounds.localBucketCap_threshold h
  rw [vertexLoad, div_le_iff₀ hp]
  nlinarith
end ThreeSum.TrimScales
