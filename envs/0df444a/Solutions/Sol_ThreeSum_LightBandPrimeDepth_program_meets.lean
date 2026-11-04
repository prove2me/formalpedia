-- Prove2me | solution 1 for ThreeSum.LightBandPrimeDepth.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:08:01.181225+00:00
-- url     : https://prove2.me/submissions/7e27eee9-e0ac-4e9a-9832-d6631324536d

import Definitions.Def_Submission_ThreeSum_Scales
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Logs
import Definitions.Def_Submission_ThreeSum_LightBandPrimeDepth
import Definitions.Def_WeightedCache3SUM_Alias_984b86210e82afdf

set_option autoImplicit false
open ThreeSum ThreeSum.LightBandPrimeDepth
open Light
set_option maxHeartbeats 1200000
set_option maxRecDepth 8000
variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ} {R y : ℕ}
namespace ThreeSum.LightBandPrimeDepth
theorem _root_.solution (hy : 0 < y) (hword : (word R y : ℤ) ≤ lim.word) :
    Meets lim program 0 d [R,y] μ (time R y)
      (fun result ν => result=(depth R y : ℤ) ∧ ν=μ) := meets rfl hy hword
end ThreeSum.LightBandPrimeDepth
