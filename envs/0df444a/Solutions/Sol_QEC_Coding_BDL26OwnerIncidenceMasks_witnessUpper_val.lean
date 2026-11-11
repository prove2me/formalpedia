-- Prove2me | solution 1 for QEC.Coding.BDL26OwnerIncidenceMasks.witnessUpper_val
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T07:27:40.616299+00:00
-- url     : https://prove2.me/submissions/83fecdca-34b5-4514-ae04-99c747c932cd

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_History
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerParentObstruction
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TopOwnerIsolation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_HistoryWitness
import Theorems.Thm_QEC_Coding_BDL26OwnerIncidenceMasks_witnessLower_val

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26OwnerIncidenceMasks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerParentObstruction BDL26ReplacementSupport
open MultiscaleDecoder
open scoped Classical
namespace QEC.Coding.BDL26OwnerIncidenceMasks
theorem _root_.solution : witnessUpper.val = evidenceUpperSyndrome := by
  change ((indexedDecoderData scaleFive 4).selectedMap (3 : StepIndex 4)).map2 witnessLower.val = _
  rw [witnessLower_val]
  rfl
end QEC.Coding.BDL26OwnerIncidenceMasks
