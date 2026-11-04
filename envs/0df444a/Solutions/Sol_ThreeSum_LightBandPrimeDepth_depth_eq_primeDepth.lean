-- Prove2me | solution 1 for ThreeSum.LightBandPrimeDepth.depth_eq_primeDepth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:59:40.076551+00:00
-- url     : https://prove2.me/submissions/98cd6d78-44b1-442f-afca-a9bffc0dad97

import Definitions.Def_Submission_ThreeSum_Scales
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Logs
import Definitions.Def_Submission_ThreeSum_LightBandPrimeDepth

set_option autoImplicit false
open ThreeSum ThreeSum.LightBandPrimeDepth
open Light
set_option maxHeartbeats 1200000
set_option maxRecDepth 8000
variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ} {R y : ℕ}
namespace ThreeSum.LightBandPrimeDepth
theorem _root_.solution (n : ℕ) :
    depth (Scales.radix n) (Scales.primeWindow n)=Scales.primeDepth Scales.radix n := rfl
end ThreeSum.LightBandPrimeDepth
