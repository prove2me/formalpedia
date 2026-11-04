-- Prove2me | solution 1 for ThreeSum.LightSourceRowFlag.flag_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:48:51.788736+00:00
-- url     : https://prove2.me/submissions/ff34d0eb-46d5-42c3-80eb-8a3046dada2e

import Definitions.Def_Submission_ThreeSum_LightSourceRowScan
import Definitions.Def_Submission_ThreeSum_LightSourceFlagTest
import Definitions.Def_Submission_ThreeSum_LightResidues
import Definitions.Def_Submission_ThreeSum_LightSourceRowFlag
import Theorems.Thm_ThreeSum_LightSourceFlagTest_flag_le


set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceRowFlag
open Light
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
namespace ThreeSum.LightSourceRowFlag
theorem _root_.solution (L h p cap : ℕ) (bits w0 w1 hist : ℕ → ℕ) :
    flag L h p cap bits w0 w1 hist ≤ 1 := LightSourceFlagTest.flag_le ..
end ThreeSum.LightSourceRowFlag
