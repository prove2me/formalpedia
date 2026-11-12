-- Prove2me | solution 1 for QEC.Coding.BDL26RXInfluenceBounds.sigmaPlusError_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:44:05.355625+00:00
-- url     : https://prove2.me/submissions/2aba6341-8a93-427e-9aea-e25e98b67b5b

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCoarseInfluence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformReadoutWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXInfluenceBounds

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXInfluenceBounds
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RXDecoderAdapter BDL26RXCoarseInfluence BDL26BoundedValence
open BDL26GraphQuantitativeBounds BDL26RZMap1CoordinateBridge
open MultiscaleDecoder RXCoarseGraining RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2 = 0)
namespace QEC.Coding.BDL26RXInfluenceBounds
theorem _root_.solution (sigma : (indexedFamily S depth).Syndrome i.succ)
    (e : (indexedFamily S depth).Cochain1 i.succ) :
    (sigmaPlusError S depth i sigma e).val =
      sigma.val + (indexedFamily S depth).coboundary1 i.succ e := rfl
end QEC.Coding.BDL26RXInfluenceBounds
