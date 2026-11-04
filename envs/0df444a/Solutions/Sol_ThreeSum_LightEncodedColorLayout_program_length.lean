-- Prove2me | solution 1 for ThreeSum.LightEncodedColorLayout.program_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:16:55.604132+00:00
-- url     : https://prove2.me/submissions/0c0e5ae4-f7db-460b-9e10-9a3dc6f920d9

import Definitions.Def_Submission_ThreeSum_EncodedColorLayout
import Definitions.Def_Submission_ThreeSum_LightEncodedColorLayout

set_option autoImplicit false
open ThreeSum ThreeSum.LightEncodedColorLayout
open Light BandPartition EncodedColorLayout
set_option maxHeartbeats 2200000
set_option maxRecDepth 11000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightEncodedColorLayout
theorem _root_.solution : program.length=2 := rfl
end ThreeSum.LightEncodedColorLayout
