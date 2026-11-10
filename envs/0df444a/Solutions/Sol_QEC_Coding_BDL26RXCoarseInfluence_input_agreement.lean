-- Prove2me | solution 1 for QEC.Coding.BDL26RXCoarseInfluence.input_agreement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T05:26:04.035375+00:00
-- url     : https://prove2.me/submissions/388c6040-aa0c-449a-a062-e40fcdd91932

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCoarseInfluence
import Theorems.Thm_QEC_Coding_BDL26RXCoarseInfluence_basisSyndrome_zero_on_readRegion

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXCoarseInfluence
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RXDecoderAdapter MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
namespace QEC.Coding.BDL26RXCoarseInfluence
theorem _root_.solution (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (h : i.val % 2 = 0) (sigma : (indexedFamily S depth).Syndrome i.succ)
    (q : FamilyQ S depth i.succ) (z : FamilyZ S depth i.castSucc)
    (hz : z ∉ influence S depth i h q) (p : FamilyZ S depth i.succ)
    (hp : p ∈ readRegion S depth i h z) : sigma.val p = (sigmaPlus S depth i sigma q).val p := by
  change sigma.val p = sigma.val p + basisSyndrome S depth i q p
  rw [basisSyndrome_zero_on_readRegion S depth i h q z hz p hp, add_zero]
end QEC.Coding.BDL26RXCoarseInfluence
