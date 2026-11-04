-- Prove2me | solution 1 for ThreeSum.SourceBuckets.Stored.nodup_bucketList
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:23:14.579988+00:00
-- url     : https://prove2.me/submissions/a8b4a76d-0d80-41b0-9dc6-1a2d8ac4e35c

import Definitions.Def_Submission_ThreeSum_LightHistogram
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.OfFn
import Definitions.Def_Submission_ThreeSum_SourceBuckets
import Theorems.Thm_ThreeSum_SourceBuckets_offset_zero
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
theorem _root_.solution {μ : ℕ → ℤ} {key : ℕ → ℕ} {N M offsets flat r : ℕ}
    (H : Stored μ key N M offsets flat) (hkey : ∀ i < N, key i < M) (hr : r < M) :
    (bucketList μ flat (offset key N r) (count key r N)).Nodup := by
  apply List.nodup_ofFn.mpr
  intro s t he
  obtain ⟨i,hi,hki,hpi,hri⟩ := H.read_bucket hkey hr s.isLt
  obtain ⟨j,hj,hkj,hpj,hrj⟩ := H.read_bucket hkey hr t.isLt
  dsimp only at he
  rw [hri,hrj,Int.toNat_natCast,Int.toNat_natCast] at he
  subst j
  apply Fin.ext
  omega
end Stored
end ThreeSum.SourceBuckets
