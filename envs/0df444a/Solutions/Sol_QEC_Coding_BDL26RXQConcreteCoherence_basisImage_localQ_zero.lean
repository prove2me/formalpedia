-- Prove2me | solution 1 for QEC.Coding.BDL26RXQConcreteCoherence.basisImage_localQ_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T23:03:52.434722+00:00
-- url     : https://prove2.me/submissions/5a13a5a8-ec5f-4af0-a3ff-dea5981fa92b

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXQBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXQConcreteCoherence
import Theorems.Thm_QEC_Coding_BDL26RXQConcreteCoherence_syndromeRegion_parent_none
import Theorems.Thm_QEC_Coding_BDL26RXQConcreteCoherence_oldZ_pair_parent
import Theorems.Thm_QEC_Coding_BDL26RXQConcreteCoherence_basisImage_mem_iff
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
theorem _root_.solution (h : i.val%2=0)
    (q t : (state S i.val).presentation.Q) (p : FamilyZ S depth i.succ)
    (hp : p ∈ (rxLq S depth i h).syndromeRegion t) :
    basisImage S depth i q p=0 := by
  by_contra hn
  have hm : p ∈ hammingSupport (basisImage S depth i q) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn⟩
  obtain ⟨z,copy,_,hv⟩ := (basisImage_mem_iff S depth i h q p).mp hm
  have he := (oldZ_pair_parent S depth i h z copy).symm.trans
    ((congrArg (fun p => parent S (i.val+1) (Vertex.z p)) hv).trans
      (syndromeRegion_parent_none S depth i h t p hp))
  cases he
end QEC.Coding.BDL26RXQConcreteCoherence
