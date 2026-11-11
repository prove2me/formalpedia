-- Prove2me | solution 1 for QEC.Coding.BDL26PairedHistoryQueryCone.rx_region_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T10:21:49.533201+00:00
-- url     : https://prove2.me/submissions/80466a44-aec9-4390-99d2-9828cd09f25c

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_PairedHistoryQueryCone_LocalReads
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_PairedHistoryQueryCone_ReadBounds
import Theorems.Thm_QEC_Coding_BDL26BoundedValence_state_boundedValence
import Theorems.Thm_QEC_Coding_BDL26GraphQuantitativeBounds_rxSyndromeFiber_card_le
import Theorems.Thm_QEC_Coding_BDL26RXQConcreteCoherence_topCenter_chart
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RXCoarseGraining_RXCoarseGrainingData_rxXiLocalComplex_region_mem_iff
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
theorem _root_.solution (h : i.val % 2 = 0) (v : Owners S depth i) :
    ((rxXiLocalComplex (rxData S depth i h)).syndromeRegion v).card ≤
      localCoordinateBound S := by
  let E := BDL26RXQConcreteCoherence.physicalZEquiv S depth i h
  let P := (state S i.val).presentation
  have hc : ((rxXiLocalComplex (rxData S depth i h)).syndromeRegion v).card ≤
      Fintype.card {r : BDL26RXLocalReplacement.RX2 P S //
        BDL26ReplacementSupport.rxSyndromeOwner P S r = vertexEquiv P v} := by
    rw [Fintype.card_subtype]
    apply Finset.card_le_card_of_injOn E.symm
    · intro p hp
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      have ht := BDL26RXQConcreteCoherence.topCenter_chart S depth i h (E.symm p)
      rw [E.apply_symm_apply] at ht
      rw [(rxXiLocalComplex_region_mem_iff _ _ _).mp hp] at ht
      exact ht.symm
    · exact E.symm.injective.injOn
  exact hc.trans (rxSyndromeFiber_card_le P (BDL26BoundedValence.state_boundedValence S i.val)
    S (vertexEquiv P v))
end QEC.Coding.BDL26PairedHistoryQueryCone
