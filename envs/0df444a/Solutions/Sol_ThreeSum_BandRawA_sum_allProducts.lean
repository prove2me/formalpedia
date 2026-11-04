-- Prove2me | solution 1 for ThreeSum.BandRawA.sum_allProducts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:41:39.556769+00:00
-- url     : https://prove2.me/submissions/0cb468a9-5603-46bb-aa0f-21d1b0d5096e

import Definitions.Def_Submission_ThreeSum_BandRawAIndex
import Definitions.Def_Submission_ThreeSum_BandWeightedScore
import Definitions.Def_Submission_ThreeSum_BandRawAProduct
import Theorems.Thm_ThreeSum_BandRawA_ownerProduct_disjoint

set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows Finset
open scoped BigOperators
set_option maxHeartbeats 1900000
set_option maxRecDepth 8000
namespace ThreeSum.BandRawA
theorem _root_.solution (F : (ℕ × ℕ × ℕ) → ℕ) (nA nB nC g : ℕ)
    (rs : List Record) :
    (∑ t ∈ allProducts nA nB nC g rs, F t)=
      ∑ s ∈ range rs.length, ∑ t ∈ ownerProduct nA nB nC g rs s, F t := by
  unfold allProducts
  apply sum_biUnion
  intro s hs t ht hst
  exact ownerProduct_disjoint (mem_range.mp hs) (mem_range.mp ht) hst
end ThreeSum.BandRawA
