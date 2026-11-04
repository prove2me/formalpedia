-- Prove2me | solution 1 for ThreeSum.SourceBuckets.count_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:31:44.530468+00:00
-- url     : https://prove2.me/submissions/4099f405-83f8-43b0-8caf-5a549b053f53

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
theorem _root_.solution (key : ℕ → ℕ) (r : ℕ) : Monotone (count key r) := by
  intro i j hij
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono hij))
end ThreeSum.SourceBuckets
