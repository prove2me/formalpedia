-- Prove2me | solution 1 for QEC.Coding.BDL26RXQConcreteCoherence.syndromeRegion_parent_none
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T10:11:19.633457+00:00
-- url     : https://prove2.me/submissions/a5704800-e68a-4e9c-88b9-f4e9571585bd

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXQBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXQConcreteCoherence
import Theorems.Thm_QEC_Coding_BDL26RXQConcreteCoherence_syndromeRegion_eq_raw
import Theorems.Thm_QEC_Coding_BDL26RXQConcreteCoherence_physicalZ_parent
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
    (q : (state S i.val).presentation.Q) (p : FamilyZ S depth i.succ)
    (hp : p ∈ (rxLq S depth i h).syndromeRegion q) :
    parent S (i.val+1) (Vertex.z p)=none := by
  rw [syndromeRegion_eq_raw] at hp
  obtain ⟨r,hr,rfl⟩ := Finset.mem_map.mp hp
  have ho := (Finset.mem_filter.mp hr).2
  have hz : rxParent (state S i.val).presentation S (Vertex.z r)=none := by
    rcases r with (⟨x,f⟩ | ⟨t,e⟩) | ⟨z,c⟩
    · cases ho
    · rfl
    · cases ho
  exact (physicalZ_parent S depth i h r).trans hz
end QEC.Coding.BDL26RXQConcreteCoherence
