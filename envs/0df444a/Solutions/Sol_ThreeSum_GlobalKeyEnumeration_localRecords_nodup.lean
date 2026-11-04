-- Prove2me | solution 1 for ThreeSum.GlobalKeyEnumeration.localRecords_nodup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:34:11.184718+00:00
-- url     : https://prove2.me/submissions/d73ab61d-9421-4935-a44d-89a193331a77

import Definitions.Def_Submission_ThreeSum_RadixKeyLists
import Definitions.Def_Submission_ThreeSum_LocalMaskGraph
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.ProdSigma
import Definitions.Def_Submission_ThreeSum_GlobalKeyEnumeration
import Theorems.Thm_ThreeSum_GlobalKeyEnumeration_layers_nodup

set_option autoImplicit false
open ThreeSum ThreeSum.GlobalKeyEnumeration
open GlobalEncoding LocalGraph LocalCoverBounds LocalHashMoments
open RadixKeyLists
open scoped BigOperators
set_option maxHeartbeats 1800000
namespace ThreeSum.GlobalKeyEnumeration
theorem _root_.solution (h : ℕ) : (localRecords h).Nodup :=
  (List.nodup_finRange _).product (layers_nodup h)
end ThreeSum.GlobalKeyEnumeration
