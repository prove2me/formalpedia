-- Prove2me | solution 1 for ThreeSum.LightArray.source_read_cast
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:28:36.401763+00:00
-- url     : https://prove2.me/submissions/e90839e0-d938-41bc-93df-21b0a9cd2a13

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Copy
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tactics
import Definitions.Def_Submission_ThreeSum_LightArray
import Theorems.Thm_ThreeSum_LightArray_source_read

set_option autoImplicit false
open ThreeSum ThreeSum.LightArray
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightArray
theorem _root_.solution {μ : ℕ → ℤ} {src dst n j : ℕ} {f : ℕ → ℤ}
    (h : SourceSafe src dst n) (hj : j < n) :
    wrote μ dst f j ((src : ℤ) + (j : ℤ)).toNat = μ (src + j) := by
  have hc : ((src : ℤ) + (j : ℤ)).toNat = src + j := by
    exact_mod_cast (Int.toNat_of_nonneg (a := (src : ℤ) + (j : ℤ)) (by positivity))
  rw [hc]
  exact source_read h hj
end ThreeSum.LightArray
