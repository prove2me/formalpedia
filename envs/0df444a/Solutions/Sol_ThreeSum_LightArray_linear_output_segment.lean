-- Prove2me | solution 1 for ThreeSum.LightArray.linear_output_segment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:17:51.901477+00:00
-- url     : https://prove2.me/submissions/bb1f625c-2a59-44da-a66d-5d6470791a2e

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Copy
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tactics
import Definitions.Def_Submission_ThreeSum_LightArray
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
open ThreeSum ThreeSum.LightArray
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightArray
theorem _root_.solution {μ μ' : ℕ → ℤ} {srcA srcB dst n : ℕ}
    {c : ℤ} {as bs : List ℤ} (hA : Seg μ srcA as) (hB : Seg μ srcB bs)
    (hlenA : as.length = n) (hlenB : bs.length = n)
    (hout : ∀ i < n, μ' (dst + i) = μ (srcA + i) + c * μ (srcB + i)) :
    Seg μ' dst (List.zipWith (fun a b => a + c * b) as bs) := by
  intro i hi
  have hin : i < n := by simpa only [List.length_zipWith, hlenA, hlenB, min_self] using hi
  rw [List.getElem_zipWith, hout i hin, hA i (by omega), hB i (by omega)]
end ThreeSum.LightArray
