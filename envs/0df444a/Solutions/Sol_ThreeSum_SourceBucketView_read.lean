-- Prove2me | solution 1 for ThreeSum.SourceBucketView.read
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:22:51.010199+00:00
-- url     : https://prove2.me/submissions/43c7ffab-c663-45d9-a667-2f770fdae02b

import Definitions.Def_Submission_ThreeSum_SourceBuckets
import Definitions.Def_Submission_ThreeSum_SourceBucketView
import Theorems.Thm_ThreeSum_SourceBucketView_start_eq
import Theorems.Thm_ThreeSum_SourceBucketView_length_eq
import Theorems.Thm_ThreeSum_SourceBuckets_Stored_read_bucket


set_option autoImplicit false
open ThreeSum ThreeSum.SourceBucketView
open SourceBuckets LightHistogram
namespace ThreeSum.SourceBucketView
theorem _root_.solution {μ : ℕ → ℤ} {key : ℕ → ℕ} {N M offsets flat r t : ℕ}
    (H : Stored μ key N M offsets flat) (hkey : ∀ i < N, key i < M)
    (hr : r < M) (ht : t < length μ offsets r) :
    ∃ i < N, key i = r ∧ μ (flat+start μ offsets r+t) = (i : ℤ) := by
  rw [length_eq H hr] at ht
  rw [start_eq H (Nat.le_of_lt hr)]
  obtain ⟨i,hi,hki,_,hread⟩ := H.read_bucket hkey hr ht
  exact ⟨i,hi,hki,hread⟩
end ThreeSum.SourceBucketView
