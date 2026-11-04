-- Prove2me | solution 1 for ThreeSum.SourceBuckets.Stored.mem_bucketList_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:23:13.405547+00:00
-- url     : https://prove2.me/submissions/12b40a55-a6ed-4407-a5a0-5d8ef40f3222

import Definitions.Def_Submission_ThreeSum_LightHistogram
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.OfFn
import Definitions.Def_Submission_ThreeSum_SourceBuckets
import Theorems.Thm_ThreeSum_SourceBuckets_offset_zero
import Theorems.Thm_ThreeSum_SourceBuckets_count_strict
import Theorems.Thm_ThreeSum_SourceBuckets_Stored_read_bucket
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
namespace Stored
theorem _root_.solution {μ : ℕ → ℤ} {key : ℕ → ℕ} {N M offsets flat r i : ℕ}
    (H : Stored μ key N M offsets flat) (hkey : ∀ i < N, key i < M) (hr : r < M) :
    i ∈ bucketList μ flat (offset key N r) (count key r N) ↔ i < N ∧ key i = r := by
  simp only [bucketList,List.mem_ofFn]
  constructor
  · rintro ⟨t,he⟩
    obtain ⟨j,hj,hkj,_,hread⟩ := H.read_bucket hkey hr t.isLt
    rw [hread,Int.toNat_natCast] at he
    subst i
    exact ⟨hj,hkj⟩
  · rintro ⟨hi,hki⟩
    have ht : count key r i < count key r N := count_strict hi hki
    refine ⟨⟨count key r i,ht⟩,?_⟩
    have he := H.indices i hi
    unfold position at he
    rw [hki] at he
    simpa only [Nat.add_assoc,Int.toNat_natCast] using congrArg Int.toNat he
end Stored
end ThreeSum.SourceBuckets
