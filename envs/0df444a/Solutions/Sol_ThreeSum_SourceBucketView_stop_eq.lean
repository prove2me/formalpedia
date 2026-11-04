-- Prove2me | solution 1 for ThreeSum.SourceBucketView.stop_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:57:41.916213+00:00
-- url     : https://prove2.me/submissions/74c9a3ee-c75f-4fb5-b096-c18dd3154a4e

import Definitions.Def_Submission_ThreeSum_SourceBuckets
import Definitions.Def_Submission_ThreeSum_SourceBucketView

set_option autoImplicit false
open ThreeSum ThreeSum.SourceBucketView
open SourceBuckets LightHistogram
namespace ThreeSum.SourceBucketView
theorem _root_.solution {μ : ℕ → ℤ} {key : ℕ → ℕ} {N M offsets flat r : ℕ}
    (H : Stored μ key N M offsets flat) (hr : r < M) :
    stop μ offsets r = offset key N (r+1) := by
  unfold stop
  rw [Nat.add_assoc,H.offsets (r+1) (by omega),Int.toNat_natCast]
end ThreeSum.SourceBucketView
