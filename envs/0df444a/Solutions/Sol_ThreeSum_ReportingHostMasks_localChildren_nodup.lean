-- Prove2me | solution 1 for ThreeSum.ReportingHostMasks.localChildren_nodup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:30:47.539882+00:00
-- url     : https://prove2.me/submissions/87123f5c-01fb-419a-b2a2-e465b4360be8

import Definitions.Def_Submission_ThreeSum_BlockMaskLayout
import Definitions.Def_Submission_ThreeSum_QueryCoordinates
import Definitions.Def_Submission_ThreeSum_ReportingHostMasks
import Definitions.Def_WeightedCache3SUM_Alias_ae0f877763340798
import Theorems.Thm_ThreeSum_ReportingHostMasks_globalChildren_nodup
import Theorems.Thm_ThreeSum_QueryCoordinates_missingSets_mem


set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostMasks
open Finset BlockRows BlockIndex BlockIndexedQuery BlockMaskLayout
open ThreeSum.SubsetAddress StoredReporting BlockForced
namespace ThreeSum.ReportingHostMasks
theorem _root_.solution {J L : ℕ} (i : Fin J) (Q : Finset (Fin L)) (h : ℕ) :
    (localChildren i Q h).Nodup := by
  apply (globalChildren_nodup i Q h).map_on
  intro S hS T hT he
  have hs := (QueryCoordinates.missingSets_mem _ _ _).mp hS
  have ht := (QueryCoordinates.missingSets_mem _ _ _).mp hT
  rw [← blockSet_localRow i Q hs.1,← blockSet_localRow i Q ht.1,he]
end ThreeSum.ReportingHostMasks
