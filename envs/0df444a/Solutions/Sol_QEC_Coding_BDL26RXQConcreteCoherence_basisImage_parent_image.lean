-- Prove2me | solution 1 for QEC.Coding.BDL26RXQConcreteCoherence.basisImage_parent_image
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T23:04:13.561551+00:00
-- url     : https://prove2.me/submissions/21978cb4-4df1-4677-bdf5-2c9a1e4c64c6

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXQBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXQConcreteCoherence
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
theorem _root_.solution (h : i.val%2=0) (q : (state S i.val).presentation.Q) :
    (hammingSupport (basisImage S depth i q)).image
      (fun p => parent S (i.val+1) (Vertex.z p)) =
      (BDL26RXQBlockTransport.incidentZ S i q).image (fun z => some (Vertex.z z)) := by
  ext u
  constructor
  · intro hu
    obtain ⟨p,hp,hpu⟩ := Finset.mem_image.mp hu
    obtain ⟨z,copy,hz,hv⟩ := (basisImage_mem_iff S depth i h q p).mp hp
    apply Finset.mem_image.mpr
    refine ⟨z,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hz⟩,?_⟩
    exact (oldZ_pair_parent S depth i h z copy).symm.trans
      ((congrArg (fun p => parent S (i.val+1) (Vertex.z p)) hv).trans hpu)
  · intro hu
    obtain ⟨z,hz,hzu⟩ := Finset.mem_image.mp hu
    let p := ((rxData S depth i h).induced.zPairEquiv (z,0)).val
    apply Finset.mem_image.mpr
    refine ⟨p,(basisImage_mem_iff S depth i h q p).mpr
      ⟨z,0,(Finset.mem_filter.mp hz).2,rfl⟩,?_⟩
    exact (oldZ_pair_parent S depth i h z 0).trans hzu
end QEC.Coding.BDL26RXQConcreteCoherence
