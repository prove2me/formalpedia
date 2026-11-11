-- Prove2me | solution 1 for QEC.Coding.BDL26OwnerIncidenceMasks.witnessTopOutput_coarse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T07:27:59.2132+00:00
-- url     : https://prove2.me/submissions/dc8601e0-0b5d-4ceb-9dc1-dc923862cea4

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_History
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerParentObstruction
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TopOwnerIsolation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_HistoryWitness
import Theorems.Thm_QEC_Coding_BDL26RZDecoderAdapter_rzStepOutput_map2_coarse


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26OwnerIncidenceMasks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerParentObstruction BDL26ReplacementSupport
open MultiscaleDecoder
open scoped Classical
namespace QEC.Coding.BDL26OwnerIncidenceMasks
theorem _root_.solution : witnessTopOutput.coarse = witnessLower := by
  change (actualStep scaleFive 4 (3 : StepIndex 4) witnessUpper).coarse = witnessLower
  rw [actualStep_rz scaleFive 4 3 (by decide)]
  exact BDL26RZDecoderAdapter.rzStepOutput_map2_coarse scaleFive 4 3 (by decide) witnessLower
end QEC.Coding.BDL26OwnerIncidenceMasks
