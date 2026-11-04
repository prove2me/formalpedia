-- Prove2me | solution 1 for ThreeSum.BlockSourceEncoding.modulus_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:43:47.723508+00:00
-- url     : https://prove2.me/submissions/6bec91dc-4d6b-4d7f-ad10-dc1378dbe765

import Definitions.Def_Submission_ThreeSum_BlockIndexedQuery
import Definitions.Def_Submission_ThreeSum_LightSourceHistogram
import Definitions.Def_Submission_ThreeSum_BlockSourceEncoding
import Theorems.Thm_ThreeSum_LocalCoverBounds_localPrime_pos


set_option autoImplicit false
open ThreeSum ThreeSum.BlockSourceEncoding
open Finset BlockEncoding GlobalEncoding LocalCoverBounds LightSourceResidues
open scoped BigOperators
set_option maxHeartbeats 1000000
namespace ThreeSum.BlockSourceEncoding
theorem _root_.solution (h J : ℕ) : 0 < modulus h J := pow_pos (localPrime_pos h) J
end ThreeSum.BlockSourceEncoding
