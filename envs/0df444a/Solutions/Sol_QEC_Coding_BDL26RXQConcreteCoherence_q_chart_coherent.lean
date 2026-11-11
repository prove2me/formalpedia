-- Prove2me | solution 1 for QEC.Coding.BDL26RXQConcreteCoherence.q_chart_coherent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T10:28:10.114804+00:00
-- url     : https://prove2.me/submissions/823f71f1-f4a4-4504-98b7-df6a609fa964

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXQBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXQConcreteCoherence
import Theorems.Thm_QEC_Coding_BDL26RXQConcreteCoherence_correctionOwner_chart
import Theorems.Thm_QEC_Coding_BDL26RXQConcreteCoherence_correctionRegion_parent_iff
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_rxQVertexEquiv_val
import Theorems.Thm_QEC_Coding_BDL26RZMap1CoordinateBridge_tannerCoboundary1_canonicalBasis_apply
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
    (q : (state S i.val).presentation.Q)
    (v : QDoubleCylinderVertex (state S i.val).presentation q S) :
    (rxQVertexEquiv S depth i h q v).val =
      rxPhysicalQEquiv S depth i h (.inr ⟨q,v⟩) ∧
    vertexEquiv (state S i.val).presentation
      (correctionOwnerAt S depth i h (rxQVertexEquiv S depth i h q v).val)=Vertex.q q ∧
    parent S (i.val+1) (Vertex.q (rxQVertexEquiv S depth i h q v).val)=some (Vertex.q q) := by
  refine ⟨rxQVertexEquiv_val S depth i h q v,?_,?_⟩
  · rw [rxQVertexEquiv_val,correctionOwner_chart]
    rfl
  · exact (correctionRegion_parent_iff S depth i h q _).mp
      (rxQVertexEquiv S depth i h q v).property
end QEC.Coding.BDL26RXQConcreteCoherence
