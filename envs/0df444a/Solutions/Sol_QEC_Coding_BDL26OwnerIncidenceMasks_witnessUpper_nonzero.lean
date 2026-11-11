-- Prove2me | solution 1 for QEC.Coding.BDL26OwnerIncidenceMasks.witnessUpper_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T07:32:11.90988+00:00
-- url     : https://prove2.me/submissions/bf7f9c65-0998-4ab4-90b1-565f6ccb96e5

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_History
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerParentObstruction
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TopOwnerIsolation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_HistoryWitness
import Theorems.Thm_QEC_Coding_BDL26OwnerIncidenceMasks_witnessUpper_val
import Theorems.Thm_QEC_Coding_BDL26OwnerParentObstruction_evidenceUpperSyndrome_nonzero


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26OwnerIncidenceMasks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerParentObstruction BDL26ReplacementSupport
open MultiscaleDecoder
open scoped Classical
namespace QEC.Coding.BDL26OwnerIncidenceMasks
theorem _root_.solution : witnessUpper.val ≠ 0 := by
  rw [witnessUpper_val]
  exact evidenceUpperSyndrome_nonzero
end QEC.Coding.BDL26OwnerIncidenceMasks
