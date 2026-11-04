-- Prove2me | solution 1 for ThreeSum.GlobalKeyEnumeration.layers_nodup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:29:48.19262+00:00
-- url     : https://prove2.me/submissions/34e065ad-155d-41bf-b3b6-333754094c9a

import Definitions.Def_Submission_ThreeSum_RadixKeyLists
import Definitions.Def_Submission_ThreeSum_LocalMaskGraph
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.ProdSigma
import Definitions.Def_Submission_ThreeSum_GlobalKeyEnumeration
import Theorems.Thm_ThreeSum_GlobalKeyEnumeration_layerRecord_injective

set_option autoImplicit false
open ThreeSum ThreeSum.GlobalKeyEnumeration
open GlobalEncoding LocalGraph LocalCoverBounds LocalHashMoments
open RadixKeyLists
open scoped BigOperators
set_option maxHeartbeats 1800000
namespace ThreeSum.GlobalKeyEnumeration
theorem _root_.solution (h : ℕ) : (layers h).Nodup :=
  List.nodup_ofFn_ofInjective (layerRecord_injective h)
end ThreeSum.GlobalKeyEnumeration
