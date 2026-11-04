-- Prove2me | solution 1 for ThreeSum.LightOutputDecodeDivide.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:24:41.915775+00:00
-- url     : https://prove2.me/submissions/fcac04e0-ff1e-40f2-b683-6442357ffb53

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Emod
import Definitions.Def_Submission_ThreeSum_LightOutputDecodeDivide
import Theorems.Thm_ThreeSum_LightOutputDecodeDivide_bounded_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightOutputDecodeDivide
open Light Light.Emod
set_option maxHeartbeats 1800000
set_option maxRecDepth 7000
variable {lim : Limits} {P : Program} {d : ℕ} {μ ν : ℕ → ℤ} {a Mo V fr : ℕ}
namespace ThreeSum.LightOutputDecodeDivide
theorem _root_.solution (F : Pre lim Mo V fr) (haV : a ≤ V) :
    Meets lim program 0 d [a,Mo,fr] μ (budget V)
      (fun q ν => q = ((a/Mo : ℕ) : ℤ) ∧ Kept μ ν fr) := bounded_meets rfl F haV
end ThreeSum.LightOutputDecodeDivide
