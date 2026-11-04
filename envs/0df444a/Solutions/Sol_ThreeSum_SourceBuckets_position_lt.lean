-- Prove2me | solution 1 for ThreeSum.SourceBuckets.position_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:41:02.316457+00:00
-- url     : https://prove2.me/submissions/8e35caf7-3a2a-441e-b06c-a363bc980763

import Definitions.Def_Submission_ThreeSum_LightHistogram
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.OfFn
import Definitions.Def_Submission_ThreeSum_SourceBuckets
import Theorems.Thm_ThreeSum_SourceBuckets_offset_le
import Theorems.Thm_ThreeSum_SourceBuckets_position_end

set_option autoImplicit false
open ThreeSum ThreeSum.SourceBuckets
open Finset LightHistogram
set_option maxHeartbeats 1400000
set_option maxRecDepth 10000
namespace ThreeSum.SourceBuckets
theorem _root_.solution {key : ℕ → ℕ} {N M i : ℕ} (hkey : ∀ i < N, key i < M) (hi : i < N) :
    position key N i < N :=
  (position_end hi).trans_le (offset_le hkey (by have hk := hkey i hi; omega))
end ThreeSum.SourceBuckets
