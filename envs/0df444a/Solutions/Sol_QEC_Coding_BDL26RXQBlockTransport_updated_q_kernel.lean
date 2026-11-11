-- Prove2me | solution 1 for QEC.Coding.BDL26RXQBlockTransport.updated_q_kernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T10:30:13.151599+00:00
-- url     : https://prove2.me/submissions/5680ea93-eae5-4ea7-b51a-f7a7154fdd64

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXErrorPullback
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXQBlockTransport
import Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_error_x_zero
import Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_updated_supported
import Theorems.Thm_QEC_Coding_BDL26IndexedDecoder_selectedMap_eq
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_map2_auxiliary_zero
import Theorems.Thm_QEC_Coding_BDL26RXErrorPullback_updated_delta
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

section
noncomputable section
namespace QEC.Coding.BDL26RXQBlockTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)
private theorem selected_rx :
    (indexedDecoderData S depth).selectedMap i = (indexedDecoderData S depth).rxMap i := by
  rw [selectedMap_eq]
  rfl
private theorem actual_coboundary1 (j : LevelIndex depth) :
    (indexedDecoderData S depth).family.coboundary1 j =
      (indexedFamily S depth).coboundary1 j := rfl
private theorem actual_contract :
    (Data S depth i h).contract = rxContract S depth i h := rfl
private theorem map2_q_zero (s : (indexedFamily S depth).Cochain2 i.castSucc)
    (q : QCoord S i) : restrictWordLinear ((rxLq S depth i h).syndromeRegion q)
      (((indexedDecoderData S depth).selectedMap i).map2 s)=0 := by
  rw [selected_rx]
  funext p
  apply (Data S depth i h).induced.map2_auxiliary_zero
  rw [← (Data S depth i h).zSector_eq_induced]
  intro hz
  apply (Finset.disjoint_left.mp (Data S depth i h).sectors_pairwise_disjoint.2.2) _ hz
  rw [(Data S depth i h).qSector_eq_regions]
  exact Finset.mem_biUnion.mpr ⟨q, Finset.mem_univ _, p.property⟩
end QEC.Coding.BDL26RXQBlockTransport
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXQBlockTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)
namespace QEC.Coding.BDL26RXQBlockTransport
theorem _root_.solution (q : QCoord S i) (a b : Upper S depth i)
    (he : hammingSupport (a+b) ⊆ (rxLq S depth i h).correctionRegion q) :
    (rxContract S depth i h).rx_local_complexes.cqDelta1 q
      (restrictWordLinear ((rxLq S depth i h).correctionRegion q)
        (updated S depth i h a b))=0 := by
  have hk := (Data S depth i h).contract.support_decomposition.cqDelta1_restriction_global q
    (updated S depth i h a b)
    (error_x_zero S depth i h q _ (updated_supported S depth i h q a b he))
  rw [actual_contract S depth i h, actual_coboundary1 S depth] at hk
  rw [updated_delta, map2_q_zero] at hk
  exact hk.symm
end QEC.Coding.BDL26RXQBlockTransport
