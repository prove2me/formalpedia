-- Prove2me | solution 1 for ThreeSum.LightSourceBandBanksProgram.program_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:19:32.733639+00:00
-- url     : https://prove2.me/submissions/857ecafb-6cc6-4060-8fbd-47f217f9d498

import Definitions.Def_Submission_ThreeSum_LightSourceBandBanks
import Definitions.Def_Submission_ThreeSum_LightBlockSourceBatchProgram
import Definitions.Def_Submission_ThreeSum_LightSourceBandBanksProgram

set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceBandBanksProgram
open Light
namespace ThreeSum.LightSourceBandBanksProgram
theorem _root_.solution : program.length=50 := rfl
end ThreeSum.LightSourceBandBanksProgram
