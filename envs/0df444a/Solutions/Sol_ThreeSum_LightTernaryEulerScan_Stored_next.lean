-- Prove2me | solution 1 for ThreeSum.LightTernaryEulerScan.Stored.next
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:40:19.725293+00:00
-- url     : https://prove2.me/submissions/25a4fa84-e46b-48a4-885b-7fd7da912feb

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
namespace Stored
theorem _root_.solution {μ ν ξ : ℕ → ℤ} {f : ℕ → ℤ} {rank : ℕ → ℕ}
    {vals current fr j : ℕ} (H : Stored μ ν f rank vals current fr j)
    (hrank : rank j=current) (hwrite : ξ (vals+j)=f j)
    (hkeep : ∀ a < fr, a ≠ vals+j → ξ a=ν a) :
    Stored μ ξ f rank vals current fr (j+1) := by
  intro a ha
  by_cases he : a=vals+j
  · subst a
    simpa [stageValue,hrank] using hwrite
  · rw [hkeep a ha he, H a ha, stageValue_succ_of_ne μ f rank he]
end Stored
end ThreeSum.LightTernaryEulerScan
