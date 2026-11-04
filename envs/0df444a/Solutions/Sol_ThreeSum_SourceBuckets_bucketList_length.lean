-- Prove2me | solution 1 for ThreeSum.SourceBuckets.bucketList_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:14:05.874196+00:00
-- url     : https://prove2.me/submissions/a37fdbd3-14df-423e-9410-dac4b5bb3000

import Definitions.Def_Submission_ThreeSum_LightHistogram
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.OfFn
import Definitions.Def_Submission_ThreeSum_SourceBuckets
import Theorems.Thm_ThreeSum_SourceBuckets_offset_zero
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_LightHistogram_count_zero
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.LightHistogram.count_zero


attribute [local simp] ThreeSum.SourceBuckets.offset_zero

set_option autoImplicit false
open ThreeSum ThreeSum.SourceBuckets
open Finset LightHistogram
set_option maxHeartbeats 1400000
set_option maxRecDepth 10000
namespace ThreeSum.SourceBuckets
theorem _root_.solution (μ : ℕ → ℤ) (flat start length : ℕ) :
    (bucketList μ flat start length).length = length := by simp [bucketList]
end ThreeSum.SourceBuckets
