-- Prove2me | solution 1 for ThreeSum.ReportingHostMasks.localChild_validPrefix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:37:39.43598+00:00
-- url     : https://prove2.me/submissions/7e3600e8-7cf1-4c65-b103-6b522626a084

import Definitions.Def_Submission_ThreeSum_BlockMaskLayout
import Definitions.Def_Submission_ThreeSum_QueryCoordinates
import Definitions.Def_Submission_ThreeSum_ReportingHostMasks
import Definitions.Def_WeightedCache3SUM_Alias_7fc1926665073fa8
import Theorems.Thm_ThreeSum_ReportingHostMasks_validPrefix_append
import Theorems.Thm_ThreeSum_RawReporting_mem_childList


set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostMasks
open Finset BlockRows BlockIndex BlockIndexedQuery BlockMaskLayout
open ThreeSum.SubsetAddress StoredReporting BlockForced
namespace ThreeSum.ReportingHostMasks
theorem _root_.solution {h J k : ℕ} (q : GlobalEncoding.GlobalOutput h J)
    (pre : List (Finset (Fin (512*h)))) (hp : ValidPrefix q k pre) (hk : k < J)
    (S : Finset (Fin (512*h)))
    (hS : S ∈ localChildren ⟨k,hk⟩ (outputRows q ⟨k,hk⟩) h) :
    ValidPrefix q (k+1) (pre ++ [S]) := by
  exact validPrefix_append q pre hp hk S
    (Finset.mem_powersetCard.mp (RawReporting.mem_childList.mp
      ((localChildren_mem _ _ _ _).mp hS)))
end ThreeSum.ReportingHostMasks
