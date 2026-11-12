-- Prove2me | solution 1 for QEC.Coding.BDL26RXQConcreteCoherence.correctionRegion_localRegion_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T23:02:05.490199+00:00
-- url     : https://prove2.me/submissions/9b7fa944-f61b-4bd2-98be-fd12942949a6

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXQBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXQConcreteCoherence
import Theorems.Thm_QEC_Coding_BDL26RXQConcreteCoherence_correctionRegion_parent_iff
import Theorems.Thm_QEC_Coding_BDL26RZMap1CoordinateBridge_tannerCoboundary1_canonicalBasis_apply
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
attribute [local simp] QEC.Coding.BDL26RZMap1CoordinateBridge.tannerCoboundary1_canonicalBasis_apply



set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXQConcreteCoherence
open MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData (cqComponentTotal)
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26DecodingGraph BDL26IndexedDecoder BDL26AlternatingCochain
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXDecoderAdapter
open BDL26RZMap1CoordinateBridge
  (tannerCoboundary0 tannerCoboundary1 tannerCoboundary1_canonicalBasis_apply)
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)
namespace QEC.Coding.BDL26RXQConcreteCoherence
theorem _root_.solution (h : i.val%2=0)
    (q : (state S i.val).presentation.Q) (p : FamilyQ S depth i.succ) :
    p ∈ (rxLq S depth i h).correctionRegion q ↔
      Vertex.q p ∈ localRegion S (i.val+1) (Vertex.q q) :=
  (correctionRegion_parent_iff S depth i h q p).trans
    (parent_mem_iff S (i.val+1) (Vertex.q q) (Vertex.q p))
end QEC.Coding.BDL26RXQConcreteCoherence
