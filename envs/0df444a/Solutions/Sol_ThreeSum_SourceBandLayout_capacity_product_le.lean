-- Prove2me | solution 1 for ThreeSum.SourceBandLayout.capacity_product_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:32:45.472141+00:00
-- url     : https://prove2.me/submissions/9746e0cf-095a-49f4-bfbd-e414acfb0d4a

import Definitions.Def_Submission_ThreeSum_BandPartition
import Definitions.Def_Submission_ThreeSum_LightSourceBucketOriginal
import Definitions.Def_Submission_ThreeSum_SourceBucketView
import Definitions.Def_Submission_ThreeSum_SourceBandLayout
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_BandPartition_size_mul_le
import Theorems.Thm_ThreeSum_LightHistogram_count_zero
import Theorems.Thm_ThreeSum_SourceBuckets_offset_zero
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.LightHistogram.count_zero
attribute [local simp] ThreeSum.SourceBuckets.offset_zero



set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandLayout
open BandPartition LightHistogram SourceBuckets
namespace ThreeSum.SourceBandLayout
theorem _root_.solution (n g : ℕ) (hg : 0 < g) : size n g*cap n g ≤ 2*n := by
  by_cases hgn : g ≤ n
  · rw [cap,min_eq_right hgn]
    exact (size_mul_le n g).trans (by omega)
  · by_cases hn : n=0
    · simp [hn,cap]
    · have hdiv : (n-1)/g=0 := Nat.div_eq_of_lt (by omega)
      simp only [cap,min_eq_left (by omega : n ≤ g),size,if_neg hn,hdiv,zero_add,one_mul]
      omega
end ThreeSum.SourceBandLayout
