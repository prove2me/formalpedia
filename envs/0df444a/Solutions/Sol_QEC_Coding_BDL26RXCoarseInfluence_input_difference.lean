-- Prove2me | solution 1 for QEC.Coding.BDL26RXCoarseInfluence.input_difference
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:10:57.703415+00:00
-- url     : https://prove2.me/submissions/27571c16-0c14-46a2-99ef-351e3b9ef1c7

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
    sigma.val + (sigmaPlus S depth i sigma q).val = basisSyndrome S depth i q := by
  funext p
  change sigma.val p + (sigma.val p + basisSyndrome S depth i q p) = _
  rw [← add_assoc, ZModModule.add_self, zero_add]
end QEC.Coding.BDL26RXCoarseInfluence
