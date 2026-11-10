-- Prove2me | solution 1 for QEC.Coding.BDL26RXDecoderAdapter.rxStepOutput_component_supported
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T05:19:07.388887+00:00
-- url     : https://prove2.me/submissions/5ed58cd7-6cff-4018-b427-9ae962ca37fe

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
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RXCoarseGraining_RXCoarseGrainingData_rx_component_supported


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
    (j : Fin (rxStepOutput S depth i h sigma).localComponents.length) :
    (rxStepOutput S depth i h sigma).componentSupportAt j ⊆
      (rxXiLocalComplex (rxData S depth i h)).correctionRegion (componentOwner S depth i h sigma j) := by
  rw [AssemblyStepOutput.componentSupportAt_eq, rxStepOutput_component_eq]
  intro p hp
  by_contra hout
  have hz := rx_component_supported (rxData S depth i h)
    (componentOwner S depth i h sigma j) sigma.val p hout
  have hn := (Finset.mem_filter.mp hp).2
  exact hn hz
end QEC.Coding.BDL26RXDecoderAdapter
