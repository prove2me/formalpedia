-- Prove2me | solution 1 for QEC.Coding.BDL26OwnerIncidenceMasks.witnessTopOutput_boundary_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:18:16.94087+00:00
-- url     : https://prove2.me/submissions/60fc05c1-c2e8-4c68-8245-ec0a3947dda2

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_History
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerParentObstruction
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TopOwnerIsolation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_HistoryWitness
import Theorems.Thm_QEC_Coding_BDL26RZDecoderAdapter_rzStepOutput_map2_component_boundary_zero


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26OwnerIncidenceMasks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerParentObstruction BDL26ReplacementSupport
open MultiscaleDecoder
open scoped Classical
namespace QEC.Coding.BDL26OwnerIncidenceMasks
theorem _root_.solution
    (j : Fin witnessTopOutput.localComponents.length) :
    witnessTopOutput.componentCoboundaryAt j = 0 :=
  BDL26RZDecoderAdapter.rzStepOutput_map2_component_boundary_zero
    scaleFive 4 3 (by decide) witnessLower j
end QEC.Coding.BDL26OwnerIncidenceMasks
