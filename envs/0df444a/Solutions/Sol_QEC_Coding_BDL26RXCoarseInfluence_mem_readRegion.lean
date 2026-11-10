-- Prove2me | solution 1 for QEC.Coding.BDL26RXCoarseInfluence.mem_readRegion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T05:04:31.559843+00:00
-- url     : https://prove2.me/submissions/65028dbc-d0a1-4b3f-8c75-131ef111751e

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
    (h : i.val % 2 = 0) (z : FamilyZ S depth i.castSucc) (p : FamilyZ S depth i.succ) :
    p ∈ readRegion S depth i h z ↔
      ∃ v ∈ xiIndexSet (rxData S depth i h).levelGraph.graph
        ((rxData S depth i h).coarseCenter z) 2,
        p ∈ (rxXiLocalComplex (rxData S depth i h)).syndromeRegion v :=
  Finset.mem_biUnion
end QEC.Coding.BDL26RXCoarseInfluence
