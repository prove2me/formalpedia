-- Prove2me | solution 1 for QEC.Coding.BDL26RXErrorPullback.embedded_coarse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T09:57:00.634697+00:00
-- url     : https://prove2.me/submissions/8ca768cd-2731-4ae9-b5bf-17f1b7136146

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXErrorPullback_EmbeddedReadout
import Theorems.Thm_QEC_Coding_BDL26RXErrorPullback_embedded_correction_eq_zero_input
import Theorems.Thm_QEC_Coding_BDL26IndexedDecoder_selectedMap_eq
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_map2_diagonal
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_rxStepOutput_correction
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_rxStepOutput_relation
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_rxStepOutput_weight
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXErrorPullback
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RXDecoderAdapter MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2 = 0)
namespace QEC.Coding.BDL26RXErrorPullback
theorem _root_.solution (tau : (indexedFamily S depth).Syndrome i.castSucc) :
    (rxStepOutput S depth i h (embeddedSyndrome S depth i h tau)).coarse.val = tau.val := by
  let sigma0 : (indexedFamily S depth).Syndrome i.succ := ⟨0, ⟨0, map_zero _⟩⟩
  have hc : (rxStepOutput S depth i h (embeddedSyndrome S depth i h tau)).correction =
      (rxStepOutput S depth i h sigma0).correction := by
    rw [rxStepOutput_correction, rxStepOutput_correction]
    exact embedded_correction_eq_zero_input S depth i h tau.val
  have hz : (rxStepOutput S depth i h sigma0).coarse.val = 0 := by
    apply (HammingWeight_eq_zero_iff _).mp
    have hw := rxStepOutput_weight S depth i h sigma0
    have hs0 : sigma0.val = 0 := rfl
    rw [hs0, HammingWeight_zero] at hw
    omega
  have hr0 := rxStepOutput_relation S depth i h sigma0
  change (0 : (indexedFamily S depth).Cochain2 i.succ) = _ at hr0
  rw [hz, map_zero, add_zero] at hr0
  have hr := rxStepOutput_relation S depth i h (embeddedSyndrome S depth i h tau)
  rw [hc, ← hr0, zero_add] at hr
  have hsel : (indexedDecoderData S depth).selectedMap i = (indexedDecoderData S depth).rxMap i := by
    rw [selectedMap_eq]
    rfl
  rw [hsel] at hr
  change ((indexedDecoderData S depth).rxMap i).map2 tau.val = _ at hr
  funext z
  have he := congrFun hr ((Data S depth i h).induced.zPairEquiv (z,0)).val
  rw [(Data S depth i h).induced.map2_diagonal, (Data S depth i h).induced.map2_diagonal] at he
  exact he.symm
end QEC.Coding.BDL26RXErrorPullback
