-- Prove2me | solution 1 for QEC.Coding.BDL26RXCoarseInfluence.coarse_eq_outside_influence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T05:41:01.289843+00:00
-- url     : https://prove2.me/submissions/5c890def-fcc5-4b5e-ab59-ebcc458dba0e

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCoarseInfluence
import Theorems.Thm_QEC_Coding_BDL26RXCoarseInfluence_aggregate_agreement
import Theorems.Thm_QEC_Coding_BDL26RXCoarseInfluence_canonical_coarse
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RXCoarseGraining_RXCoarseGrainingData_rx_coarse_word_invariant_at_center
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXCoarseInfluence
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RXDecoderAdapter MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
namespace QEC.Coding.BDL26RXCoarseInfluence
theorem _root_.solution (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (h : i.val % 2 = 0) (_hi : 2 ≤ i.val) (sigma : (indexedFamily S depth).Syndrome i.succ)
    (q : FamilyQ S depth i.succ) (z : FamilyZ S depth i.castSucc)
    (hz : z ∉ influence S depth i h q) :
    (rxStepOutput S depth i h sigma).coarse.val z =
      (rxStepOutput S depth i h (sigmaPlus S depth i sigma q)).coarse.val z := by
  rw [canonical_coarse, canonical_coarse]
  exact (rx_coarse_word_invariant_at_center (rxData S depth i h) sigma.val z).trans
    ((congrArg (fun word => rxCoarseWord (rxData S depth i h) word z)
      (aggregate_agreement S depth i h sigma q z hz)).trans
        (rx_coarse_word_invariant_at_center (rxData S depth i h)
          (sigmaPlus S depth i sigma q).val z).symm)
end QEC.Coding.BDL26RXCoarseInfluence
