-- Prove2me | solution 1 for QEC.Coding.BDL26OwnerIncidenceMasks.witnessUpperError_syndrome
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:19:11.262714+00:00
-- url     : https://prove2.me/submissions/cd9600e5-c5a2-481d-9c68-8baac3d22ccd

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
theorem _root_.solution :
    (indexedFamily scaleFive 4).coboundary1 (4 : LevelIndex 4) witnessUpperError = witnessUpper.val := by
  exact LinearMap.congr_fun
    (((indexedDecoderData scaleFive 4).selectedMap (3 : StepIndex 4)).commutes_coboundary1)
    evidenceCorrection
end QEC.Coding.BDL26OwnerIncidenceMasks
