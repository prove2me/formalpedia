-- Prove2me | solution 1 for QEC.Coding.BDL26HistorySyndromeSensitivity.rz_pair_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T09:58:45.937287+00:00
-- url     : https://prove2.me/submissions/4eb41d9d-cc42-4c34-b57a-de2f63d5bc59

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXInfluenceBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_History
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Steps
import Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_binary_add_eq_zero_iff
import Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_mem_rzPropagation
import Theorems.Thm_QEC_Coding_BDL26RZDecoderAdapter_rzStepOutput_coarse_apply


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
theorem _root_.solution (h : ¬ i.val % 2 = 0)
    (sigma tau : (indexedFamily S depth).Syndrome i.succ) :
    hammingSupport ((rzStepOutput S depth i h sigma).coarse.val +
      (rzStepOutput S depth i h tau).coarse.val) ⊆
      rzPropagation S depth i h (hammingSupport (sigma.val + tau.val)) := by
  intro z hz
  by_contra hn
  have hag : ∀ p ∈ (rzData S depth i h).coarseRegion z, sigma.val p = tau.val p := by
    intro p hp
    apply (binary_add_eq_zero_iff _ _).mp
    by_contra hsum
    apply hn
    exact (mem_rzPropagation S depth i h _ z).mpr
      ⟨p,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hsum⟩,hp⟩
  have he : (rzStepOutput S depth i h sigma).coarse.val z =
      (rzStepOutput S depth i h tau).coarse.val z := by
    rw [rzStepOutput_coarse_apply, rzStepOutput_coarse_apply]
    exact Finset.sum_congr rfl hag
  exact (Finset.mem_filter.mp hz).2 ((binary_add_eq_zero_iff _ _).mpr he)
end QEC.Coding.BDL26HistorySyndromeSensitivity
