-- Prove2me | solution 1 for QEC.Coding.BDL26OwnerIncidenceMasks.witnessLower_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T09:31:37.772942+00:00
-- url     : https://prove2.me/submissions/041c197e-45ce-42b2-a8ca-facdbb229bf7

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_History
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerParentObstruction
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TopOwnerIsolation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_HistoryWitness
import Theorems.Thm_QEC_Coding_BDL26OwnerIncidenceMasks_witnessLower_val
import Theorems.Thm_QEC_Coding_BDL26OwnerParentObstruction_evidenceLowerSyndrome_nonzero


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26OwnerIncidenceMasks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerParentObstruction BDL26ReplacementSupport
open MultiscaleDecoder
open scoped Classical
namespace QEC.Coding.BDL26OwnerIncidenceMasks
theorem _root_.solution : witnessLower.val ≠ 0 := by
  rw [witnessLower_val]
  exact evidenceLowerSyndrome_nonzero
end QEC.Coding.BDL26OwnerIncidenceMasks
