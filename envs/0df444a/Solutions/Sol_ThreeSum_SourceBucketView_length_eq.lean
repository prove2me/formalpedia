-- Prove2me | solution 1 for ThreeSum.SourceBucketView.length_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:01:33.594197+00:00
-- url     : https://prove2.me/submissions/6d66c722-93ba-460a-b02f-cc8b803cfb85

import Definitions.Def_Submission_ThreeSum_SourceBuckets
import Definitions.Def_Submission_ThreeSum_SourceBucketView
import Theorems.Thm_ThreeSum_SourceBucketView_start_eq
import Theorems.Thm_ThreeSum_SourceBucketView_stop_eq
import Theorems.Thm_ThreeSum_SourceBuckets_offset_succ


set_option autoImplicit false
open ThreeSum ThreeSum.SourceBucketView
open SourceBuckets LightHistogram
namespace ThreeSum.SourceBucketView
theorem _root_.solution {μ : ℕ → ℤ} {key : ℕ → ℕ} {N M offsets flat r : ℕ}
    (H : Stored μ key N M offsets flat) (hr : r < M) :
    length μ offsets r = count key r N := by
  rw [length,start_eq H (Nat.le_of_lt hr),stop_eq H hr,offset_succ]
  omega
end ThreeSum.SourceBucketView
