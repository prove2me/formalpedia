-- Prove2me | solution 1 for SoficGroups.KunDiagonalGoodRootGraphLoss.card_goodPermutationGraph_add_graph_loss
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:58.258203+00:00
-- url     : https://prove2.me/submissions/392663a1-a70d-4c5a-a0e1-7f40c0e955f5

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunThomFiberCoarea_permutationGraph_card
import Theorems.Thm_SoficGroups_KunDiagonalGoodRootGraphLoss_goodPermutationGraph_subset

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunDiagonalGoodRootGraphLoss
open scoped BigOperators symmDiff
namespace SoficGroups.KunDiagonalGoodRootGraphLoss
theorem _root_.solution {V : Type*}
    [Fintype V] [DecidableEq V]
    (p : Equiv.Perm V) (B : Finset V) :
    (SoficGroups.permutationGraph p \ goodPermutationGraph p B).card +
        (goodPermutationGraph p B).card = Fintype.card V := by
  calc
    (SoficGroups.permutationGraph p \ goodPermutationGraph p B).card +
        (goodPermutationGraph p B).card =
        (SoficGroups.permutationGraph p).card :=
      Finset.card_sdiff_add_card_eq_card
        (goodPermutationGraph_subset p B)
    _ = Fintype.card V :=
      SoficGroups.KunThomFiberCoarea.permutationGraph_card p
end SoficGroups.KunDiagonalGoodRootGraphLoss
