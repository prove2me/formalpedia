-- Prove2me | solution 1 for ThreeSum.ReportingHostPairEnumeration.rights_nodup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:45:46.206327+00:00
-- url     : https://prove2.me/submissions/696aa377-a6ec-4c4b-b879-e34ea37a8f53

import Definitions.Def_Submission_ThreeSum_ReportingHostPrefixCatalog
import Definitions.Def_Submission_ThreeSum_QueryCoordinates
import Definitions.Def_Submission_ThreeSum_ReportingHostPairEnumeration
import Theorems.Thm_ThreeSum_QueryCoordinates_missingSets_nodup


set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostPairEnumeration
open Finset ThreeSum.SubsetAddress LayerCounts LocalGraph
set_option linter.unusedSimpArgs false
namespace ThreeSum.ReportingHostPairEnumeration
theorem _root_.solution {L : ℕ} (S : Finset (Fin L)) (h : ℕ) : (rights S h).Nodup :=
  QueryCoordinates.missingSets_nodup _ _
end ThreeSum.ReportingHostPairEnumeration
