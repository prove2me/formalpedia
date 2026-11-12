-- Prove2me | solution 1 for QEC.Coding.BDL26RXQConcreteCoherence.finite_basis_classification
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T23:05:19.796212+00:00
-- url     : https://prove2.me/submissions/7fc523e6-f155-4cc9-8f7f-1ef83442d6e7

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXQBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXQConcreteCoherence
import Theorems.Thm_QEC_Coding_BDL26RXQConcreteCoherence_q_chart_coherent
import Theorems.Thm_QEC_Coding_BDL26RXQConcreteCoherence_q_assembly_snapshot
import Theorems.Thm_QEC_Coding_BDL26RXQConcreteCoherence_basisImage_incident_value
import Theorems.Thm_QEC_Coding_BDL26RXQConcreteCoherence_basisImage_nonzero
import Theorems.Thm_QEC_Coding_BDL26RXQConcreteCoherence_connector_parent_none
import Theorems.Thm_QEC_Coding_BDL26RXQConcreteCoherence_connector_value_zero
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
theorem _root_.solution (h : i.val%2=0) (q : (state S i.val).presentation.Q) :
    (let p := (rxQVertexEquiv S depth i h q (0,Sum.inl (Sum.inl ()))).val
     p ∈ (rxLq S depth i h).correctionRegion q ∧
       parent S (i.val+1) (Vertex.q p)=some (Vertex.q q)) ∧
    ((rxStepOutput_ownerLabels S depth i h (basisInput S depth i q)).label
      (qComponentIndex S depth i h (basisInput S depth i q) q)).owner=some (Vertex.q q) ∧
    basisImage S depth i q≠0 ∧
    (∀ copy : Fin 2, basisImage S depth i q ((rxData S depth i h).induced.zPairEquiv
      (BDL26RXQBlockTransport.incidentWitness S i q,copy)).val=1) ∧
    parent S (i.val+1) (Vertex.z (connector S depth i h q))=none ∧
    basisImage S depth i q (connector S depth i h q)=0 := by
  refine ⟨⟨(rxQVertexEquiv S depth i h q (0,Sum.inl (Sum.inl ()))).property,
    (q_chart_coherent S depth i h q _).2.2⟩,?_,basisImage_nonzero S depth i h q,
    basisImage_incident_value S depth i h q,connector_parent_none S depth i h q,
    connector_value_zero S depth i h q⟩
  exact (q_assembly_snapshot S depth i h (basisInput S depth i q) q).1
end QEC.Coding.BDL26RXQConcreteCoherence
