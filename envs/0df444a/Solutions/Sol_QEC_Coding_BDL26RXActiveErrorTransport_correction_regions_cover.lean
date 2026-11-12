-- Prove2me | solution 1 for QEC.Coding.BDL26RXActiveErrorTransport.correction_regions_cover
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T10:42:07.17964+00:00
-- url     : https://prove2.me/submissions/b59549a7-ad04-401b-98e2-4e0ed0ae4dd2

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXActiveErrorTransport
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_correction_sectors_cover


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXActiveErrorTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge BDL26RXXStarTransport MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open BDL26BoundedValence BDL26GraphQuantitativeBounds
open scoped BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)
namespace QEC.Coding.BDL26RXActiveErrorTransport
theorem _root_.solution :
    (Finset.univ.biUnion ((rxLx S depth i h).correctionRegion)) ∪
      (Finset.univ.biUnion ((rxLq S depth i h).correctionRegion))=Finset.univ := by
  have hc := (rxData S depth i h).correction_sectors_cover
  rw [(rxData S depth i h).qCorrectionSector_eq_regions] at hc
  exact hc
end QEC.Coding.BDL26RXActiveErrorTransport
