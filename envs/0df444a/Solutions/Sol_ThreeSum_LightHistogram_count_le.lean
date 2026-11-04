-- Prove2me | solution 1 for ThreeSum.LightHistogram.count_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:29:41.789802+00:00
-- url     : https://prove2.me/submissions/6139b115-38c3-4f0f-8dec-c171c1944058

import Definitions.Def_Submission_ThreeSum_LightArray
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range
import Definitions.Def_Submission_ThreeSum_LightHistogram
import Theorems.Thm_ThreeSum_LightHistogram_count_zero
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast


attribute [local simp] ThreeSum.LightHistogram.count_zero

set_option autoImplicit false
open ThreeSum ThreeSum.LightHistogram
open Light Finset
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightHistogram
theorem _root_.solution (key : ℕ → ℕ) (r i : ℕ) : count key r i ≤ i := by
  exact (Finset.card_filter_le _ _).trans (by simp)
end ThreeSum.LightHistogram
