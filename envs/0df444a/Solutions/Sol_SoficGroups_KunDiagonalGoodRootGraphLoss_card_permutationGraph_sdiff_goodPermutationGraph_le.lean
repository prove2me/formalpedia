-- Prove2me | solution 1 for SoficGroups.KunDiagonalGoodRootGraphLoss.card_permutationGraph_sdiff_goodPermutationGraph_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:58.258203+00:00
-- url     : https://prove2.me/submissions/57e73c46-1542-42a1-af01-949a5ea7bc57

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunDiagonalGoodRootGraphLoss_card_filter_permutationGraph_fst_mem
import Theorems.Thm_SoficGroups_KunDiagonalGoodRootGraphLoss_card_filter_permutationGraph_snd_mem
import Theorems.Thm_SoficGroups_KunDiagonalGoodRootGraphLoss_permutationGraph_sdiff_goodPermutationGraph_subset

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunDiagonalGoodRootGraphLoss
open scoped BigOperators symmDiff
namespace SoficGroups.KunDiagonalGoodRootGraphLoss
theorem _root_.solution {V : Type*}
    [Fintype V] [DecidableEq V]
    (p : Equiv.Perm V) (B : Finset V) :
    (SoficGroups.permutationGraph p \ goodPermutationGraph p B).card ≤
      2 * B.card := by
  calc
    (SoficGroups.permutationGraph p \ goodPermutationGraph p B).card ≤
        (((SoficGroups.permutationGraph p).filter fun z => z.1 ∈ B) ∪
          ((SoficGroups.permutationGraph p).filter
            fun z => z.2 ∈ B)).card :=
      Finset.card_le_card
        (permutationGraph_sdiff_goodPermutationGraph_subset p B)
    _ ≤ ((SoficGroups.permutationGraph p).filter
          fun z => z.1 ∈ B).card +
        ((SoficGroups.permutationGraph p).filter
          fun z => z.2 ∈ B).card := Finset.card_union_le _ _
    _ = 2 * B.card := by
      rw [card_filter_permutationGraph_fst_mem,
        card_filter_permutationGraph_snd_mem]
      omega
end SoficGroups.KunDiagonalGoodRootGraphLoss
