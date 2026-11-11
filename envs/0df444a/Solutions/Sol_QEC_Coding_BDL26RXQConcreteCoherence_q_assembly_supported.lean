-- Prove2me | solution 1 for QEC.Coding.BDL26RXQConcreteCoherence.q_assembly_supported
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T10:11:37.405823+00:00
-- url     : https://prove2.me/submissions/d9cd4c39-aeb3-47cf-a46e-9d52407f9f54

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXQBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXQConcreteCoherence
import Theorems.Thm_QEC_Coding_BDL26RXQConcreteCoherence_qComponentIndex_owner
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_rxStepOutput_component_supported
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
    (q : (state S i.val).presentation.Q) :
    (rxStepOutput S depth i h sigma).componentSupportAt
      (qComponentIndex S depth i h sigma q) ⊆ (rxLq S depth i h).correctionRegion q := by
  have hs := rxStepOutput_component_supported S depth i h sigma (qComponentIndex S depth i h sigma q)
  rw [qComponentIndex_owner] at hs
  exact hs
end QEC.Coding.BDL26RXQConcreteCoherence
