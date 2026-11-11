-- Prove2me | solution 1 for QEC.Coding.BDL26RXInfluenceBounds.coarse_eq_outside_errorInfluence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T10:13:29.211694+00:00
-- url     : https://prove2.me/submissions/3315d76c-1e20-4647-b661-0e7beb1258df

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCoarseInfluence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformReadoutWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXInfluenceBounds
import Theorems.Thm_QEC_Coding_BDL26RXInfluenceBounds_aggregate_agreement
import Theorems.Thm_QEC_Coding_BDL26RXCoarseInfluence_aggregate_agreement
import Theorems.Thm_QEC_Coding_BDL26RXCoarseInfluence_canonical_coarse
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RXCoarseGraining_RXCoarseGrainingData_rx_coarse_word_invariant_at_center
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXInfluenceBounds
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RXDecoderAdapter BDL26RXCoarseInfluence BDL26BoundedValence
open BDL26GraphQuantitativeBounds BDL26RZMap1CoordinateBridge
open MultiscaleDecoder RXCoarseGraining RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2 = 0)
namespace QEC.Coding.BDL26RXInfluenceBounds
theorem _root_.solution (hi : 2 ≤ i.val)
    (sigma : (indexedFamily S depth).Syndrome i.succ)
    (e : (indexedFamily S depth).Cochain1 i.succ) (z : FamilyZ S depth i.castSucc)
    (hz : z ∉ errorInfluence S depth i h e) :
    (rxStepOutput S depth i h sigma).coarse.val z =
      (rxStepOutput S depth i h (sigmaPlusError S depth i sigma e)).coarse.val z := by
  rw [canonical_coarse, canonical_coarse]
  exact (rx_coarse_word_invariant_at_center (rxData S depth i h) sigma.val z).trans
    ((congrArg (fun word => rxCoarseWord (rxData S depth i h) word z)
      (aggregate_agreement S depth i h sigma e z hz)).trans
        (rx_coarse_word_invariant_at_center (rxData S depth i h)
          (sigmaPlusError S depth i sigma e).val z).symm)
end QEC.Coding.BDL26RXInfluenceBounds
