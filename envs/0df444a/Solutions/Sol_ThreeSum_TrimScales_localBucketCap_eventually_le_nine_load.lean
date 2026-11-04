-- Prove2me | solution 1 for ThreeSum.TrimScales.localBucketCap_eventually_le_nine_load
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:21:10.048615+00:00
-- url     : https://prove2.me/submissions/2d3dfde6-f71f-4ae0-9d87-aea049cd4a08

import Definitions.Def_Submission_ThreeSum_Scales
import Definitions.Def_Submission_ThreeSum_LocalHashMoments
import Definitions.Def_Submission_ThreeSum_TrimScales
import Theorems.Thm_ThreeSum_TrimScales_vertexLoad_eventually_ge_one
import Theorems.Thm_ThreeSum_LocalCoverBounds_bucketCap_real_bound
import Theorems.Thm_ThreeSum_LocalCoverBounds_localPrime_pos


set_option autoImplicit false
open ThreeSum ThreeSum.TrimScales
open Filter Real ThreeSum.Scales
open scoped Topology
noncomputable section
namespace ThreeSum.TrimScales
theorem _root_.solution :
    ∀ᶠ h : ℕ in atTop, (LocalCoverBounds.localBucketCap h : ℝ) ≤ 9 * vertexLoad h := by
  filter_upwards [vertexLoad_eventually_ge_one] with h hh
  have hu := LocalCoverBounds.bucketCap_real_bound (V := LocalCoverBounds.vertexCount (512 * h) h)
    (LocalCoverBounds.localPrime_pos h)
  change (LocalCoverBounds.localBucketCap h : ℝ) <
    5 + 4 * (LocalCoverBounds.vertexCount (512 * h) h : ℝ) / LocalCoverBounds.localPrime h at hu
  change (LocalCoverBounds.localBucketCap h : ℝ) ≤
    9 * ((LocalCoverBounds.vertexCount (512 * h) h : ℝ) / LocalCoverBounds.localPrime h)
  change 1 ≤ (LocalCoverBounds.vertexCount (512 * h) h : ℝ) / LocalCoverBounds.localPrime h at hh
  rw [mul_div_assoc] at hu
  linarith
end ThreeSum.TrimScales
