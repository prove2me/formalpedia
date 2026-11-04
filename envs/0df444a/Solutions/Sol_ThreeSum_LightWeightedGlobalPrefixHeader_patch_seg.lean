-- Prove2me | solution 1 for ThreeSum.LightWeightedGlobalPrefixHeader.patch_seg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T17:31:46.623188+00:00
-- url     : https://prove2.me/submissions/b8e3db6f-3d79-4667-b648-fc5fbc51dfcf

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixHeader
import Definitions.Def_Submission_Weighted_Global_TernaryPrefixHeaderSegment
import Theorems.Thm_ThreeSum_LightWeightedGlobalPrefixHeader_store_seg

set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedGlobalPrefixHeader
open Light
set_option maxHeartbeats 4000000
namespace ThreeSum.LightWeightedGlobalPrefixHeader
theorem _root_.solution {μ : ℕ→ℤ} {base : ℕ} {xs : List ℤ} (hs : Seg μ base xs)
    (loc : ℕ→ℤ) (fs : List (ℕ×ℕ)) :
    Seg (patch base loc μ fs) base (patchList loc xs fs) :=by
  induction fs generalizing μ xs with
  | nil=>exact hs
  | cons f fs ih=>exact ih (store_seg hs f.1 (loc f.2))
end ThreeSum.LightWeightedGlobalPrefixHeader
