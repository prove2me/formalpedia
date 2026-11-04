-- Prove2me | solution 1 for ThreeSum.LightArray.source_read
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:24:29.752899+00:00
-- url     : https://prove2.me/submissions/7f41f436-7c8f-44be-b183-68550d4c0068

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Copy
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tactics
import Definitions.Def_Submission_ThreeSum_LightArray
import Theorems.Thm_Light_wrote_rest


set_option autoImplicit false
open ThreeSum ThreeSum.LightArray
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightArray
theorem _root_.solution {μ : ℕ → ℤ} {src dst n j : ℕ} {f : ℕ → ℤ}
    (h : SourceSafe src dst n) (hj : j < n) :
    wrote μ dst f j (src + j) = μ (src + j) := by
  rcases h with rfl | h
  · exact wrote_rest (by omega)
  · exact wrote_rest (by omega)
end ThreeSum.LightArray
