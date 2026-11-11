-- Prove2me | solution 1 for QEC.Coding.BDL26RXInfluenceBounds.forwardTwo_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T06:56:57.327812+00:00
-- url     : https://prove2.me/submissions/513130f4-dfaf-477b-afef-3671b2753cbc

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCoarseInfluence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformReadoutWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXInfluenceBounds
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXInfluenceBounds
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RXDecoderAdapter BDL26RXCoarseInfluence BDL26BoundedValence
open BDL26GraphQuantitativeBounds BDL26RZMap1CoordinateBridge
open MultiscaleDecoder RXCoarseGraining RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable {V : Type} [Fintype V] [DecidableEq V]
namespace QEC.Coding.BDL26RXInfluenceBounds
theorem _root_.solution (G : DirectedGraph V)
    (hdegree : ∀ u, (outNeighbors G u).card ≤ 7) (u : V) :
    (forwardTwo G u).card ≤ 57 := by
  have hbi := Finset.card_biUnion_le_card_mul (outNeighbors G u) (outNeighbors G) 7
    (fun w _ => hdegree w)
  have hu := hdegree u
  have hmul : (outNeighbors G u).card * 7 ≤ 49 := by omega
  have hsecond : ((outNeighbors G u).biUnion (outNeighbors G)).card ≤ 49 := hbi.trans hmul
  have hsum := Finset.card_union_le (outNeighbors G u)
    ((outNeighbors G u).biUnion (outNeighbors G))
  have hins := Finset.card_insert_le u
    (outNeighbors G u ∪ (outNeighbors G u).biUnion (outNeighbors G))
  change (insert u (outNeighbors G u ∪ (outNeighbors G u).biUnion (outNeighbors G))).card ≤ 57
  omega
end QEC.Coding.BDL26RXInfluenceBounds
