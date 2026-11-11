-- Prove2me | solution 1 for QEC.Coding.BDL26OwnerIncidenceMasks.witnessLower_val
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T06:53:41.317133+00:00
-- url     : https://prove2.me/submissions/1a508697-1167-4d3c-a1a4-199bf2a0084f

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_History
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerParentObstruction
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TopOwnerIsolation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_HistoryWitness

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26OwnerIncidenceMasks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerParentObstruction BDL26ReplacementSupport
open MultiscaleDecoder
open scoped Classical
namespace QEC.Coding.BDL26OwnerIncidenceMasks
theorem _root_.solution : witnessLower.val = evidenceLowerSyndrome := by
  change (indexedFamily scaleFive 4).coboundary1 (3 : LevelIndex 4) evidenceCorrection = _
  rw [indexedFamily_coboundary1]
  rfl
end QEC.Coding.BDL26OwnerIncidenceMasks
