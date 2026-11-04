-- Prove2me | solution 1 for ThreeSum.SourceBuckets.exists_bucket_position
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:17:38.805517+00:00
-- url     : https://prove2.me/submissions/fb56a4bf-6f72-4257-8cbe-76916877b66c

import Definitions.Def_Submission_ThreeSum_LightHistogram
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.OfFn
import Definitions.Def_Submission_ThreeSum_SourceBuckets
import Theorems.Thm_ThreeSum_SourceBuckets_offset_succ
import Theorems.Thm_ThreeSum_SourceBuckets_offset_le
import Definitions.Def_WeightedCache3SUM_Alias_64c7fbec3ba932da
import Theorems.Thm_ThreeSum_SourceBuckets_exists_position

set_option autoImplicit false
open ThreeSum ThreeSum.SourceBuckets
open Finset LightHistogram
set_option maxHeartbeats 1400000
set_option maxRecDepth 10000
namespace ThreeSum.SourceBuckets
theorem _root_.solution {key : ℕ → ℕ} {N M r t : ℕ}
    (hkey : ∀ i < N, key i < M) (hr : r < M) (ht : t < count key r N) :
    ∃ i < N, key i = r ∧ position key N i = offset key N r+t := by
  have htN : offset key N r+t < N := by
    have he := offset_le hkey (show r+1 ≤ M by omega)
    rw [offset_succ] at he
    omega
  obtain ⟨i,hi,he⟩ := exists_position hkey htN
  refine ⟨i,hi,?_,he⟩
  apply (position_bucket_iff hi).mp
  rw [he,offset_succ]
  omega
end ThreeSum.SourceBuckets
