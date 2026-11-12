-- Prove2me | solution 1 for QEC.Coding.BDL26RXDecoderAdapter.rxStepOutput_component_boundary_radius_actual
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:09:52.090126+00:00
-- url     : https://prove2.me/submissions/65071534-33fc-4c55-bbfe-aba6dba02068

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
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_rxStepOutput_component_boundary_radius_one
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_rxData_graph_edge
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_distance_le_one_iff


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
    (p : FamilyZ S depth i.succ)
    (hp : (rxStepOutput S depth i h sigma).componentCoboundaryAt j p ≠ 0) :
    DirectedGraph.distance (tannerLevel (state S i.val).presentation).graph
      (vertexEquiv (state S i.val).presentation (componentOwner S depth i h sigma j))
      (vertexEquiv (state S i.val).presentation ((rxData S depth i h).topCenter p)) ≤ 1 := by
  apply (distance_le_one_iff _ _ _).mpr
  have hd := rxStepOutput_component_boundary_radius_one S depth i h sigma j p hp
  rcases (distance_le_one_iff _ _ _).mp hd with he | he
  · exact Or.inl (congrArg (vertexEquiv (state S i.val).presentation) he)
  · right
    rw [← rxData_graph_edge S depth i h]
    exact he
end QEC.Coding.BDL26RXDecoderAdapter
