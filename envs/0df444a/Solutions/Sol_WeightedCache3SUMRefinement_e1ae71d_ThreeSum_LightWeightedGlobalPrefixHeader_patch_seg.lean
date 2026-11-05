-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalPrefixHeader.patch_seg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T14:21:51.987426+00:00
-- url     : https://prove2.me/submissions/9d42d88e-1179-4da0-96d2-a0cbaf9908ce

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPrefixHeader
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPrefixHeaderSegment
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalPrefixHeader_store_seg

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalPrefixHeader
open Light
set_option maxHeartbeats 4000000
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalPrefixHeader
theorem _root_.solution {μ : ℕ→ℤ} {base : ℕ} {xs : List ℤ} (hs : Seg μ base xs)
    (loc : ℕ→ℤ) (fs : List (ℕ×ℕ)) :
    Seg (patch base loc μ fs) base (patchList loc xs fs) :=by
  induction fs generalizing μ xs with
  | nil=>exact hs
  | cons f fs ih=>exact ih (store_seg hs f.1 (loc f.2))
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalPrefixHeader
