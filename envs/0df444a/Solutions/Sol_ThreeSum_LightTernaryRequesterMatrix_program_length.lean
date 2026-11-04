-- Prove2me | solution 1 for ThreeSum.LightTernaryRequesterMatrix.program_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:32:22.908936+00:00
-- url     : https://prove2.me/submissions/b9bfc07e-f45d-4edc-8fae-bb7673c8b60f

import Definitions.Def_Submission_ThreeSum_LightTernaryOriginalRequester
import Definitions.Def_Submission_ThreeSum_LightTernaryCarryCodes
import Definitions.Def_Submission_ThreeSum_LightTernarySignedMatrix
import Definitions.Def_Submission_ThreeSum_TernarySignedLayout
import Definitions.Def_Submission_ThreeSum_LightTernaryRequesterMatrix

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryRequesterMatrix
open Light TernarySignedDigits TernarySignedReduction
set_option maxHeartbeats 6000000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {depth : ℕ}
namespace ThreeSum.LightTernaryRequesterMatrix
theorem _root_.solution : program.length=8 := rfl
end ThreeSum.LightTernaryRequesterMatrix
