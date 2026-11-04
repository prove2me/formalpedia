-- Prove2me | solution 1 for ThreeSum.LightOriginalBucketFilter.bad_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:04:48.432003+00:00
-- url     : https://prove2.me/submissions/01bca8cd-f5f2-485b-a9ea-0e2cf3168e07

import Definitions.Def_Submission_ThreeSum_LightHistogram
import Definitions.Def_Submission_ThreeSum_LightOriginalBucketFilter
import Theorems.Thm_ThreeSum_LightOriginalBucketFilter_good_zero
import Theorems.Thm_ThreeSum_LightOriginalBucketFilter_bad_zero
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


attribute [local simp] ThreeSum.LightOriginalBucketFilter.good_zero
attribute [local simp] ThreeSum.LightOriginalBucketFilter.bad_zero

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightOriginalBucketFilter
open Light
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
namespace ThreeSum.LightOriginalBucketFilter
theorem _root_.solution (keys counts : ℕ → ℕ) (n : ℕ) :
    bad keys counts (n+1)=bad keys counts n++if counts (keys n)=1 then [] else [n] := by
  by_cases h : counts (keys n)=1 <;> simp [bad,List.range_succ,List.filter_append,h]
end ThreeSum.LightOriginalBucketFilter
