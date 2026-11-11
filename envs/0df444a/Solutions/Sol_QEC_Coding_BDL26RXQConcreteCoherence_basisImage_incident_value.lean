-- Prove2me | solution 1 for QEC.Coding.BDL26RXQConcreteCoherence.basisImage_incident_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T08:00:05.554047+00:00
-- url     : https://prove2.me/submissions/f046a56a-4d55-4ede-8fb5-7cbec83ef99c

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXQBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXQConcreteCoherence
import Theorems.Thm_QEC_Coding_BDL26RXQConcreteCoherence_basisImage_pair
import Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_incidentWitness_mem
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
    (q : (state S i.val).presentation.Q) (copy : Fin 2) :
    basisImage S depth i q ((rxData S depth i h).induced.zPairEquiv
      (BDL26RXQBlockTransport.incidentWitness S i q,copy)).val=1 := by
  rw [basisImage_pair,if_pos (BDL26RXQBlockTransport.incidentWitness_mem S i q)]
end QEC.Coding.BDL26RXQConcreteCoherence
