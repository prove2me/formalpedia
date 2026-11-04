-- Prove2me | solution 1 for ThreeSum.GlobalKeyEnumeration.layerRecord_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:22:41.781066+00:00
-- url     : https://prove2.me/submissions/791339a1-819f-47e3-8638-350fa31d960e

import Definitions.Def_Submission_ThreeSum_RadixKeyLists
import Definitions.Def_Submission_ThreeSum_LocalMaskGraph
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.ProdSigma
import Definitions.Def_Submission_ThreeSum_GlobalKeyEnumeration
import Theorems.Thm_ThreeSum_LocalMaskGraph_setAt_injective


set_option autoImplicit false
open ThreeSum ThreeSum.GlobalKeyEnumeration
open GlobalEncoding LocalGraph LocalCoverBounds LocalHashMoments
open RadixKeyLists
open scoped BigOperators
set_option maxHeartbeats 1800000
namespace ThreeSum.GlobalKeyEnumeration
theorem _root_.solution (h : ℕ) : Function.Injective (layerRecord h) := by
  intro i j he
  apply Fin.ext
  exact LocalMaskGraph.setAt_injective i.isLt j.isLt (congrArg Subtype.val he)
end ThreeSum.GlobalKeyEnumeration
