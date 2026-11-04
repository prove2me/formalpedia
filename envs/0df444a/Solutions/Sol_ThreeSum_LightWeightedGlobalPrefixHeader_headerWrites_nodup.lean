-- Prove2me | solution 1 for ThreeSum.LightWeightedGlobalPrefixHeader.headerWrites_nodup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:43:04.49521+00:00
-- url     : https://prove2.me/submissions/1067b011-4372-4950-bc06-4e3a6bb3503c

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixLoop
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixHeader

set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedGlobalPrefixHeader
open Light
open LightWeightedGlobalPrefixLoop
set_option maxHeartbeats 7000000
set_option maxRecDepth 24000
namespace ThreeSum.LightWeightedGlobalPrefixHeader
theorem _root_.solution : (headerWrites.map Prod.fst).Nodup :=by decide
end ThreeSum.LightWeightedGlobalPrefixHeader
