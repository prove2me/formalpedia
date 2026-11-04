-- Prove2me | solution 1 for ThreeSum.SourceBandPartition.len_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:57:35.143916+00:00
-- url     : https://prove2.me/submissions/1c4893c8-4402-46c0-9256-82b22e4a6adf

import Definitions.Def_Submission_ThreeSum_SourceBandLayout
import Definitions.Def_Submission_ThreeSum_SourceBandPartition
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
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
open ThreeSum ThreeSum.SourceBandPartition
open BandPartition SourceBandLayout
namespace ThreeSum.SourceBandPartition
theorem _root_.solution {n g i : ℕ} (hg : 0 < g) (hi : size n g ≤ i) : len n g i=0 := by
  by_cases hn : n=0
  · simp [len,stop,hn]
  · have hdiv : (n-1)/g < i := by
      simpa only [size,if_neg hn,Nat.add_one_le_iff] using hi
    have hmul : n-1 < i*g := (Nat.div_lt_iff_lt_mul hg).mp hdiv
    have hs := stop_le n g i
    unfold len start
    omega
end ThreeSum.SourceBandPartition
