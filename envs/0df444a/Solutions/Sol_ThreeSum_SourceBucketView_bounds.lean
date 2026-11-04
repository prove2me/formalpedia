-- Prove2me | solution 1 for ThreeSum.SourceBucketView.bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:00:56.440787+00:00
-- url     : https://prove2.me/submissions/7d9cf67b-702d-47b9-b870-a7ad6126ed01

import Definitions.Def_Submission_ThreeSum_SourceBuckets
import Definitions.Def_Submission_ThreeSum_SourceBucketView
import Theorems.Thm_ThreeSum_SourceBucketView_start_eq
import Theorems.Thm_ThreeSum_SourceBucketView_stop_eq
import Theorems.Thm_ThreeSum_SourceBuckets_offset_le
import Theorems.Thm_ThreeSum_SourceBuckets_offset_mono


set_option autoImplicit false
open ThreeSum ThreeSum.SourceBucketView
open SourceBuckets LightHistogram
namespace ThreeSum.SourceBucketView
theorem _root_.solution {μ : ℕ → ℤ} {key : ℕ → ℕ} {N M offsets flat r : ℕ}
    (H : Stored μ key N M offsets flat) (hkey : ∀ i < N, key i < M) (hr : r < M) :
    start μ offsets r ≤ stop μ offsets r ∧ stop μ offsets r ≤ N := by
  rw [start_eq H (Nat.le_of_lt hr),stop_eq H hr]
  exact ⟨offset_mono key N (by omega),offset_le hkey (by omega)⟩
end ThreeSum.SourceBucketView
