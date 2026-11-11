-- Prove2me | solution 1 for QEC.Coding.BDL26OwnerIncidenceMasks.witnessNextOutput_input
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T09:33:35.473509+00:00
-- url     : https://prove2.me/submissions/82b8149c-bc14-4c0d-a97c-88163f21ca74

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_History
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerParentObstruction
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TopOwnerIsolation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_HistoryWitness
import Theorems.Thm_QEC_Coding_BDL26OwnerIncidenceMasks_witnessTopOutput_coarse
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26OwnerIncidenceMasks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerParentObstruction BDL26ReplacementSupport
open MultiscaleDecoder
open scoped Classical
namespace QEC.Coding.BDL26OwnerIncidenceMasks
theorem _root_.solution : witnessNextOutput.input = witnessLower := by
  exact ((actualStep_relation scaleFive 4 (2 : StepIndex 4)).input_eq
    witnessTopOutput.coarse).trans witnessTopOutput_coarse
end QEC.Coding.BDL26OwnerIncidenceMasks
