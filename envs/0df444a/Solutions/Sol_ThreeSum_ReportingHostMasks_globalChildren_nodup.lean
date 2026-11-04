-- Prove2me | solution 1 for ThreeSum.ReportingHostMasks.globalChildren_nodup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:07:26.992098+00:00
-- url     : https://prove2.me/submissions/8695f1d9-8562-4947-818e-c353a22aeb8a

import Definitions.Def_Submission_ThreeSum_BlockMaskLayout
import Definitions.Def_Submission_ThreeSum_QueryCoordinates
import Definitions.Def_Submission_ThreeSum_ReportingHostMasks
import Theorems.Thm_ThreeSum_QueryCoordinates_missingSets_nodup


set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostMasks
open Finset BlockRows BlockIndex BlockIndexedQuery BlockMaskLayout
open ThreeSum.SubsetAddress StoredReporting BlockForced
namespace ThreeSum.ReportingHostMasks
theorem _root_.solution {J L : ℕ} (i : Fin J) (Q : Finset (Fin L)) (h : ℕ) :
    (globalChildren i Q h).Nodup := QueryCoordinates.missingSets_nodup _ _
end ThreeSum.ReportingHostMasks
