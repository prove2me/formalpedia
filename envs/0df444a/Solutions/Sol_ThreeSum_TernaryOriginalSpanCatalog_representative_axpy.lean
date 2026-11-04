-- Prove2me | solution 1 for ThreeSum.TernaryOriginalSpanCatalog.representative_axpy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:16:20.685473+00:00
-- url     : https://prove2.me/submissions/1dbb34ea-9ffa-4d24-8075-1ead003c1048

import Definitions.Def_Submission_ThreeSum_TernaryOriginalSpan
import Definitions.Def_Submission_ThreeSum_TernaryOriginalSpanCatalog
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
attribute [local simp] ThreeSum.HashFamily.hashMap_apply



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryOriginalSpanCatalog
open Finset
set_option maxHeartbeats 2000000
variable {p J : ℕ}
namespace ThreeSum.TernaryOriginalSpanCatalog
theorem _root_.solution [NeZero p] (a : ℕ) (row old : Fin J → ZMod p) (i : Fin J) :
    (((a : ZMod p) • row+old) i).val=((old i).val+a*(row i).val)%p := by
  have he : (((old i).val+a*(row i).val : ℕ) : ZMod p)=((a : ZMod p) • row+old) i := by
    simp only [Nat.cast_add,Nat.cast_mul,ZMod.natCast_zmod_val,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    ring
  rw [←he,ZMod.val_natCast]
end ThreeSum.TernaryOriginalSpanCatalog
