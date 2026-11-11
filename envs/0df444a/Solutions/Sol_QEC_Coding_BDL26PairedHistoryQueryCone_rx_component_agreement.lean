-- Prove2me | solution 1 for QEC.Coding.BDL26PairedHistoryQueryCone.rx_component_agreement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T10:17:35.113732+00:00
-- url     : https://prove2.me/submissions/bd43442e-6f09-444d-8e1a-ffa7c8673868

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Intervals
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXQConcreteCoherence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_PairedHistoryQueryCone_LocalReads
import Theorems.Thm_QEC_Coding_BDL26PairedHistoryQueryCone_mem_rxOwnerRead
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RXCoarseGraining_RXCoarseGrainingData_rxXiSignal_apply
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RXCoarseGraining_RXCoarseGrainingData_rx_local_computability_certificate
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26PairedHistoryQueryCone
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26RXDecoderAdapter BDL26RZDecoderAdapter BDL26RXCoarseInfluence
open BDL26RXInfluenceBounds BDL26GraphQuantitativeBounds
open MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)
namespace QEC.Coding.BDL26PairedHistoryQueryCone
theorem _root_.solution (h : i.val % 2 = 0) (v : Owners S depth i)
    (s t : Word BDL26Field (FamilyZ S depth i.succ))
    (ha : AgreeOn (rxOwnerRead S depth i h v) s t) :
    (rxLocalComponents (rxData S depth i h)).component v s =
      (rxLocalComponents (rxData S depth i h)).component v t := by
  have he : rxXiSignal (rxData S depth i h) s v 1 =
      rxXiSignal (rxData S depth i h) t v 1 := by
    funext p
    rw [rxXiSignal_apply,rxXiSignal_apply]
    split_ifs with hd
    · exact ha p ((mem_rxOwnerRead S depth i h v p).mpr (le_trans hd (by decide)))
    · rfl
  have hs := (rx_local_computability_certificate (rxData S depth i h)).componentInvariantAtXiOne v s
  have ht := (rx_local_computability_certificate (rxData S depth i h)).componentInvariantAtXiOne v t
  exact hs.trans ((congrArg (fun w =>
    (rxLocalComponents (rxData S depth i h)).component v w) he).trans ht.symm)
end QEC.Coding.BDL26PairedHistoryQueryCone
