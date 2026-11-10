-- Prove2me | solution 1 for QEC.Coding.BDL26RXDecoderAdapter.rxStepOutput_component_q
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T05:20:08.340315+00:00
-- url     : https://prove2.me/submissions/662936d0-f240-42e4-bc25-1c79a5516726

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
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_rxStepOutput_component_eq

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
    (sigma : (indexedFamily S depth).Syndrome i.succ)
    (j : Fin (rxStepOutput S depth i h sigma).localComponents.length)
    (q : (state S i.val).presentation.Q)
    (hj : componentOwner S depth i h sigma j = .inr (.inl q)) :
    (rxStepOutput S depth i h sigma).componentAt j = cqComponentTotal (rxData S depth i h) sigma.val q := by
  rw [rxStepOutput_component_eq, hj]
  rfl
end QEC.Coding.BDL26RXDecoderAdapter
