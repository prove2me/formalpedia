-- Prove2me | solution 1 for QEC.Coding.BDL26RXQConcreteCoherence.connector_exterior
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T08:00:34.035633+00:00
-- url     : https://prove2.me/submissions/3a140230-589b-4d4e-b61b-0b5565d79d18

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXQBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXQConcreteCoherence
import Theorems.Thm_QEC_Coding_BDL26RXQConcreteCoherence_topCenter_chart
import Theorems.Thm_QEC_Coding_BDL26RZMap1CoordinateBridge_tannerCoboundary1_canonicalBasis_apply
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm
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
    connector S depth i h q ∉ (rxData S depth i h).zSector := by
  intro hp
  rw [(rxData S depth i h).zSector_eq_regions] at hp
  change connector S depth i h q ∈
    (Finset.univ.biUnion fun z => (rxLz S depth i h).syndromeRegion z) at hp
  obtain ⟨z,_,hz⟩ := Finset.mem_biUnion.mp hp
  have hc := ((rxData S depth i h).topCenter_z_iff z (connector S depth i h q)).mp hz
  have hr := topCenter_chart S depth i h (.inl (.inr ⟨q,connectorEdge S depth i q⟩))
  have he := congrArg (vertexEquiv (state S i.val).presentation) hc
  have bad : Vertex.q q=Vertex.z z := hr.symm.trans he
  cases bad
end QEC.Coding.BDL26RXQConcreteCoherence
