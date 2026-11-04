-- Prove2me | solution 1 for ThreeSum.LightTernaryWeightedHistogram.total_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:29:55.875808+00:00
-- url     : https://prove2.me/submissions/695f2a68-62cd-4d84-b2c5-daec1ba82074

import Definitions.Def_Submission_ThreeSum_LightHistogram
import Definitions.Def_Submission_ThreeSum_LightTernaryWeightedHistogram
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



set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryWeightedHistogram
open Light Finset
open scoped BigOperators
set_option maxHeartbeats 2000000
namespace ThreeSum.LightTernaryWeightedHistogram
theorem _root_.solution (key : ℕ → ℕ) (weight : ℕ → ℤ) (r : ℕ) :
    total key weight r 0=0 := by simp [total]
end ThreeSum.LightTernaryWeightedHistogram
