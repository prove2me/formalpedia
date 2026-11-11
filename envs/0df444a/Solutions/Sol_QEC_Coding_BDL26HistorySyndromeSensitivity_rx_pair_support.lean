-- Prove2me | solution 1 for QEC.Coding.BDL26HistorySyndromeSensitivity.rx_pair_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T09:46:02.096516+00:00
-- url     : https://prove2.me/submissions/4f917dff-428b-402b-af15-24d1cabb8774

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXInfluenceBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_History
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Steps
import Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_binary_add_eq_zero_iff
import Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_rx_coarse_agreement

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26RXDecoderAdapter BDL26RZDecoderAdapter
open BDL26RXCoarseInfluence BDL26RXInfluenceBounds MultiscaleDecoder
open RXCoarseGraining RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)
namespace QEC.Coding.BDL26HistorySyndromeSensitivity
theorem _root_.solution (h : i.val % 2 = 0)
    (sigma tau : (indexedFamily S depth).Syndrome i.succ) :
    hammingSupport ((rxStepOutput S depth i h sigma).coarse.val +
      (rxStepOutput S depth i h tau).coarse.val) ⊆
      rxPropagation S depth i h (hammingSupport (sigma.val + tau.val)) := by
  intro z hz
  by_contra hn
  have he : (rxStepOutput S depth i h sigma).coarse.val z =
      (rxStepOutput S depth i h tau).coarse.val z := by
    apply rx_coarse_agreement S depth i h sigma tau z
    intro p hp
    apply (binary_add_eq_zero_iff _ _).mp
    by_contra hsum
    apply hn
    exact Finset.mem_biUnion.mpr ⟨p, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hsum⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp⟩⟩
  exact (Finset.mem_filter.mp hz).2 ((binary_add_eq_zero_iff _ _).mpr he)
end QEC.Coding.BDL26HistorySyndromeSensitivity
