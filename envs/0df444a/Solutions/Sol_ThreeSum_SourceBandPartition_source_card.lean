-- Prove2me | solution 1 for ThreeSum.SourceBandPartition.source_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:09:00.282007+00:00
-- url     : https://prove2.me/submissions/1501968d-f6b3-43c5-875f-6bc769715a97

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
theorem _root_.solution (n g i : ℕ) : (source n g i).card=len n g i := by
  simpa only [Fintype.card_fin,Fintype.card_coe] using (Fintype.card_congr (equiv n g i)).symm
end ThreeSum.SourceBandPartition
