-- Prove2me | solution 1 for ThreeSum.SourceBuckets.position_lt_of_key_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:14:04.713498+00:00
-- url     : https://prove2.me/submissions/ab868616-6ce6-41a4-87de-ecd2aa4f7f4e

import Definitions.Def_Submission_ThreeSum_LightHistogram
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.OfFn
import Definitions.Def_Submission_ThreeSum_SourceBuckets
import Theorems.Thm_ThreeSum_SourceBuckets_offset_mono
import Theorems.Thm_ThreeSum_SourceBuckets_position_start
import Theorems.Thm_ThreeSum_SourceBuckets_position_end

set_option autoImplicit false
open ThreeSum ThreeSum.SourceBuckets
open Finset LightHistogram
set_option maxHeartbeats 1400000
set_option maxRecDepth 10000
namespace ThreeSum.SourceBuckets
theorem _root_.solution {key : ℕ → ℕ} {N i j : ℕ}
    (hi : i < N) (hij : key i < key j) : position key N i < position key N j :=
  (position_end hi).trans_le ((offset_mono key N (by omega)).trans (position_start key N j))
end ThreeSum.SourceBuckets
