-- Prove2me | solution 1 for ThreeSum.SourceBuckets.position_bucket_iff_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:13:42.730864+00:00
-- url     : https://prove2.me/submissions/a1365546-afd9-457e-84aa-fa0e84b624c4

import Definitions.Def_Submission_ThreeSum_LightHistogram
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.OfFn
import Definitions.Def_Submission_ThreeSum_SourceBuckets
import Theorems.Thm_ThreeSum_SourceBuckets_offset_zero
import Theorems.Thm_ThreeSum_SourceBuckets_offset_mono
import Theorems.Thm_ThreeSum_SourceBuckets_position_start
import Theorems.Thm_ThreeSum_SourceBuckets_position_end
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
theorem _root_.solution {key : ℕ → ℕ} {N i r : ℕ} (hi : i < N) :
    offset key N r ≤ position key N i ∧ position key N i < offset key N (r+1) ↔ key i = r := by
  constructor
  · rintro ⟨ha,hb⟩
    rcases lt_trichotomy (key i) r with h | h | h
    · have he := (position_end hi).trans_le (offset_mono key N (show key i+1 ≤ r by omega))
      omega
    · exact h
    · have he := (offset_mono key N (show r+1 ≤ key i by omega)).trans (position_start key N i)
      omega
  · intro he
    have ha := position_start key N i
    have hb := position_end (key := key) hi
    simpa only [he] using And.intro ha hb
end ThreeSum.SourceBuckets
