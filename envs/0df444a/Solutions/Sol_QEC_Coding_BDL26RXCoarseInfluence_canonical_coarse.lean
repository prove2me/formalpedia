-- Prove2me | solution 1 for QEC.Coding.BDL26RXCoarseInfluence.canonical_coarse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T05:10:12.618926+00:00
-- url     : https://prove2.me/submissions/5074a070-12a0-4708-8458-aaab8bc04a76

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCoarseInfluence
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_rxStepOutput_coarse


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXCoarseInfluence
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RXDecoderAdapter MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
namespace QEC.Coding.BDL26RXCoarseInfluence
theorem _root_.solution (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (h : i.val % 2 = 0) (sigma : (indexedFamily S depth).Syndrome i.succ) :
    (rxStepOutput S depth i h sigma).coarse.val = rxCoarseWord (rxData S depth i h) sigma.val :=
  rxStepOutput_coarse S depth i h sigma
end QEC.Coding.BDL26RXCoarseInfluence
