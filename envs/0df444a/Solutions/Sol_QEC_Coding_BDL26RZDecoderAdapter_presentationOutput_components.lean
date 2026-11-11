-- Prove2me | solution 1 for QEC.Coding.BDL26RZDecoderAdapter.presentationOutput_components
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T05:57:02.457324+00:00
-- url     : https://prove2.me/submissions/3d0400ea-6524-41a8-b208-0e513fa126d7

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_IndexedDecoder
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZSupportedBoundary
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZDecoderAdapter

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RZDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open BDL26ReplacementSupport BDL26RZConcreteParity BDL26LevelTwoDistance
open MultiscaleDecoder RZCoarseGraining RZCoarseGrainingData
open BDL26AlternatingCochain BDL26ReplacementCochainMaps
open scoped Classical BigOperators
namespace QEC.Coding.BDL26RZDecoderAdapter
theorem _root_.solution (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (S : OddScale)
    (sigma : (presentationFamily P A S).Syndrome (1 : LevelIndex 1)) :
    (presentationOutput P A S sigma).localComponents =
      (Finset.univ : Finset P.Z).toList.map
        (fun z => localCorrectionComponent (presentationData P A S)
          (presentationData_localTopCohomology P A S) z sigma.val) := rfl
end QEC.Coding.BDL26RZDecoderAdapter
