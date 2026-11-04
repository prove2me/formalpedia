-- Prove2me | solution 1 for ThreeSum.LightTernaryEulerScan.stageValue_below
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:00:47.500357+00:00
-- url     : https://prove2.me/submissions/d0ebc694-adcb-4d51-b5f5-ede929c64351

import Definitions.Def_Submission_ThreeSum_LightTernaryEulerRow
import Definitions.Def_Submission_ThreeSum_LightTernaryEulerScan
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_LightTernaryWeightedSum_sum_zero
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.LightTernaryWeightedSum.sum_zero



set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryEulerScan
open Light
set_option maxHeartbeats 1800000
namespace ThreeSum.LightTernaryEulerScan
theorem _root_.solution (μ : ℕ → ℤ) (f : ℕ → ℤ) (rank : ℕ → ℕ)
    {vals current j a : ℕ} (ha : a < vals) :
    stageValue μ f rank vals current j a=μ a := by
  simp [stageValue,show ¬ vals ≤ a by omega]
end ThreeSum.LightTernaryEulerScan
