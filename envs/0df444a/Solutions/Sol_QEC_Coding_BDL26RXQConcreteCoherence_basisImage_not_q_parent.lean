-- Prove2me | solution 1 for QEC.Coding.BDL26RXQConcreteCoherence.basisImage_not_q_parent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T23:05:01.289209+00:00
-- url     : https://prove2.me/submissions/733cee7c-5460-4e83-b978-b8fe856045ba

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXQBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXQConcreteCoherence
import Theorems.Thm_QEC_Coding_BDL26RXQConcreteCoherence_oldZ_pair_parent
import Theorems.Thm_QEC_Coding_BDL26RXQConcreteCoherence_basisImage_mem_iff
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
theorem _root_.solution (h : i.val%2=0) (q : (state S i.val).presentation.Q) :
    ∃ p ∈ hammingSupport (basisImage S depth i q),
      parent S (i.val+1) (Vertex.z p)≠some (Vertex.q q) := by
  let z := BDL26RXQBlockTransport.incidentWitness S i q
  let p := ((rxData S depth i h).induced.zPairEquiv (z,0)).val
  refine ⟨p,(basisImage_mem_iff S depth i h q p).mpr
    ⟨z,0,BDL26RXQBlockTransport.incidentWitness_mem S i q,rfl⟩,?_⟩
  rw [oldZ_pair_parent]
  intro he
  cases he
end QEC.Coding.BDL26RXQConcreteCoherence
