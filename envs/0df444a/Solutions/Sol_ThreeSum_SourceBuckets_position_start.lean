-- Prove2me | solution 1 for ThreeSum.SourceBuckets.position_start
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:35:10.648516+00:00
-- url     : https://prove2.me/submissions/23be8e99-ab36-4570-8ddf-be6578c122eb

import Definitions.Def_Submission_ThreeSum_LightHistogram
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.OfFn
import Definitions.Def_Submission_ThreeSum_SourceBuckets

set_option autoImplicit false
open ThreeSum ThreeSum.SourceBuckets
open Finset LightHistogram
set_option maxHeartbeats 1400000
set_option maxRecDepth 10000
namespace ThreeSum.SourceBuckets
theorem _root_.solution (key : ℕ → ℕ) (N i : ℕ) :
    offset key N (key i) ≤ position key N i := Nat.le_add_right _ _
end ThreeSum.SourceBuckets
