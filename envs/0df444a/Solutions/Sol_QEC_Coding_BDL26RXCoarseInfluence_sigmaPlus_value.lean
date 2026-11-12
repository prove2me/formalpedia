-- Prove2me | solution 1 for QEC.Coding.BDL26RXCoarseInfluence.sigmaPlus_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:10:03.930793+00:00
-- url     : https://prove2.me/submissions/31619a8a-5d65-4293-a4fb-6c6cf89e69e2

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCoarseInfluence

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXCoarseInfluence
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RXDecoderAdapter MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
namespace QEC.Coding.BDL26RXCoarseInfluence
theorem _root_.solution (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (sigma : (indexedFamily S depth).Syndrome i.succ) (q : FamilyQ S depth i.succ) :
    (sigmaPlus S depth i sigma q).val = sigma.val + basisSyndrome S depth i q := rfl
end QEC.Coding.BDL26RXCoarseInfluence
