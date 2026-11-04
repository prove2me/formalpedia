-- Prove2me | solution 1 for ThreeSum.SourceBucketView.indices_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:04:58.496211+00:00
-- url     : https://prove2.me/submissions/bd465979-6b95-45fc-a651-f31d023a438a

import Definitions.Def_Submission_ThreeSum_SourceBuckets
import Definitions.Def_Submission_ThreeSum_SourceBucketView
import Theorems.Thm_ThreeSum_SourceBucketView_start_eq
import Theorems.Thm_ThreeSum_SourceBucketView_length_eq

set_option autoImplicit false
open ThreeSum ThreeSum.SourceBucketView
open SourceBuckets LightHistogram
namespace ThreeSum.SourceBucketView
theorem _root_.solution {μ : ℕ → ℤ} {key : ℕ → ℕ} {N M offsets flat r : ℕ}
    (H : Stored μ key N M offsets flat) (hr : r < M) :
    indices μ offsets flat r = bucketList μ flat (offset key N r) (count key r N) := by
  rw [indices,start_eq H (Nat.le_of_lt hr),length_eq H hr]
end ThreeSum.SourceBucketView
