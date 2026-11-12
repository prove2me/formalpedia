-- Prove2me | solution 1 for QEC.Coding.BDL26RXQConcreteCoherence.q_assembly_parent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T23:03:00.070971+00:00
-- url     : https://prove2.me/submissions/6f3aa3fd-b88b-4db0-ad03-ea07e89d9f69

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXQBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXQConcreteCoherence
import Theorems.Thm_QEC_Coding_BDL26RXQConcreteCoherence_correctionRegion_parent_iff
import Theorems.Thm_QEC_Coding_BDL26RXQConcreteCoherence_q_assembly_supported
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
    (sigma : (indexedFamily S depth).Syndrome i.succ)
    (q : (state S i.val).presentation.Q) (p : FamilyQ S depth i.succ)
    (hp : p ∈ (rxStepOutput S depth i h sigma).componentSupportAt
      (qComponentIndex S depth i h sigma q)) :
    parent S (i.val+1) (Vertex.q p)=some (Vertex.q q) :=
  (correctionRegion_parent_iff S depth i h q p).mp
    (q_assembly_supported S depth i h sigma q hp)
end QEC.Coding.BDL26RXQConcreteCoherence
