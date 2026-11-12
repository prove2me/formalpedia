-- Prove2me | solution 1 for QEC.Coding.BDL26RXInfluenceBounds.sigmaPlusError_basis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:44:25.787998+00:00
-- url     : https://prove2.me/submissions/61c5d84c-88c9-4a5f-a8b5-85584ef70d27

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
    (q : FamilyQ S depth i.succ) :
    sigmaPlusError S depth i sigma (canonicalBasisWord (F := BDL26Field) q) =
      sigmaPlus S depth i sigma q := rfl
end QEC.Coding.BDL26RXInfluenceBounds
