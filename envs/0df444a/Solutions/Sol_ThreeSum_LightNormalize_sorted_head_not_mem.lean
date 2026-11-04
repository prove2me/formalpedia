-- Prove2me | solution 1 for ThreeSum.LightNormalize.sorted_head_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:27:32.943619+00:00
-- url     : https://prove2.me/submissions/d0b6438e-296e-4e91-a798-63d19e9d0eae

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_MergeSort
import Mathlib.Data.List.Dedup
import Definitions.Def_Submission_ThreeSum_LightNormalize
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



set_option autoImplicit false
open ThreeSum ThreeSum.LightNormalize
open Light
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightNormalize
theorem _root_.solution {x y : ℤ} {zs : List ℤ}
    (hs : (x::y::zs).Pairwise (· ≤ ·)) (hne : x ≠ y) : x ∉ y::zs := by
  simp only [List.pairwise_cons] at hs
  intro hx
  rcases List.mem_cons.mp hx with hxy | hx
  · exact hne hxy
  · exact hne (le_antisymm (hs.1 y (by simp)) (hs.2.1 x hx))
end ThreeSum.LightNormalize
