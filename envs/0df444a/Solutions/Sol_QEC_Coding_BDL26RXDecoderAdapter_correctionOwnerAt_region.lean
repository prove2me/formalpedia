-- Prove2me | solution 1 for QEC.Coding.BDL26RXDecoderAdapter.correctionOwnerAt_region
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:06:55.768303+00:00
-- url     : https://prove2.me/submissions/e69a6642-6281-43bf-8c2d-b9a1b1de630a

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Decomposition
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Coordinates
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Flow
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Lifts
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Representative
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Graph
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Sectors
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Induced
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Budgets
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_LocalComplexes
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_IndexedDecoder
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph BDL26AlternatingCochain MultiscaleDecoder RXCoarseGraining
open BDL26RZMap1CoordinateBridge (tannerCoboundary0 tannerCoboundary1)
open scoped Classical BigOperators
open BDL26IndexedDecoder BDL26AlternatingCochain
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)
open RXCoarseGrainingData
namespace QEC.Coding.BDL26RXDecoderAdapter
theorem _root_.solution (h : i.val % 2 = 0)
    (v : RXVertex (state S i.val).presentation.X (state S i.val).presentation.Q
      (state S i.val).presentation.Z)
    (p : FamilyQ S depth i.succ) :
    p ∈ (rxXiLocalComplex (rxData S depth i h)).correctionRegion v ↔
      correctionOwnerAt S depth i h p = v := by
  let G := endpointAt S depth i h
  rcases v with x | (q | z)
  · exact G.ownerX x p
  · exact G.ownerQ q p
  · change p ∈ (∅ : Finset _) ↔ G.correctionOwner p = .inr (.inr z)
    rw [← G.ownerZ, G.zCorrectionEmpty]
end QEC.Coding.BDL26RXDecoderAdapter
