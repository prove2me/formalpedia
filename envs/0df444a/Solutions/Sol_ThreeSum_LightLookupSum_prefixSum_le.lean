-- Prove2me | solution 1 for ThreeSum.LightLookupSum.prefixSum_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:20:28.067245+00:00
-- url     : https://prove2.me/submissions/564cedde-6f80-45eb-aa34-20bc38d4d647

import Definitions.Def_Submission_ThreeSum_LightArray
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_Submission_ThreeSum_LightLookupSum
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
open ThreeSum ThreeSum.LightLookupSum
open Light Finset
open scoped BigOperators
namespace ThreeSum.LightLookupSum
theorem _root_.solution (f key : ℕ → ℕ) {n B j : ℕ}
    (hvalue : ∀ i < n, f (key i) ≤ B) (hj : j ≤ n) :
    prefixSum f key j ≤ j*B := by
  unfold prefixSum
  calc
    _ ≤ ∑ _i ∈ range j, B := sum_le_sum fun i hi => hvalue i (by
      have := mem_range.mp hi
      omega)
    _ = _ := by simp
end ThreeSum.LightLookupSum
