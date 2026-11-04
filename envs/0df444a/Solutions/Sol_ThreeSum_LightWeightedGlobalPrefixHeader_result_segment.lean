-- Prove2me | solution 1 for ThreeSum.LightWeightedGlobalPrefixHeader.result_segment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T17:45:51.416761+00:00
-- url     : https://prove2.me/submissions/667a99ce-f900-4423-a3f3-f6d48e43748c

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixHeader
import Definitions.Def_Submission_Weighted_Global_TernaryPrefixHeaderSegment
import Theorems.Thm_ThreeSum_LightWeightedGlobalPrefixHeader_store_seg
import Theorems.Thm_ThreeSum_LightWeightedGlobalPrefixHeader_patch_seg
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_ThreeSum_LightWeightedSourceCountHost_Reads_update


set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedGlobalPrefixHeader
open Light
set_option maxHeartbeats 4000000
namespace ThreeSum.LightWeightedGlobalPrefixHeader
theorem _root_.solution {μ μ₀ ν : ℕ→ℤ} {template live hdr s m p power alpha2 alphaRank localQ radix J
    N T L groups nb bank powers Fbase Gbase : ℕ} {ret : ℤ} {xs : List ℤ}
    (hlen : xs.length=106) (hxs : Seg μ template xs)
    (hcopy : ∀i<106, μ₀ (live+i)=μ (template+i))
    (hν : ν=Function.update (patch live
      (frame (args template live hdr s m p power alpha2 alphaRank localQ radix J++
        locals N T L groups nb bank powers s p power alpha2 alphaRank localQ radix Fbase Gbase++[ret]))
      μ₀ LightWeightedGlobalPrefixLoop.headerWrites) (live+104) 0) :
    Seg ν live (resultHeader xs template live hdr s m p power alpha2 alphaRank localQ radix J
      N T L groups nb bank powers Fbase Gbase ret) :=by
  have hc : Seg μ₀ live xs :=by
    intro i hi
    exact (hcopy i (by omega)).trans (hxs i hi)
  subst ν
  exact store_seg (patch_seg hc _ _) 104 0
end ThreeSum.LightWeightedGlobalPrefixHeader
