-- Prove2me | solution 1 for SoficGroups.KunDiagonalGoodRootGraphLoss.card_goodPermutationGraph_ge_card_sub_twice_bad
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:58.258203+00:00
-- url     : https://prove2.me/submissions/03f9e6aa-adcf-47b7-b577-e2201c043a12

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunDiagonalGoodRootGraphLoss_card_permutationGraph_sdiff_goodPermutationGraph_le
import Theorems.Thm_SoficGroups_KunDiagonalGoodRootGraphLoss_card_goodPermutationGraph_add_graph_loss

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunDiagonalGoodRootGraphLoss
open scoped BigOperators symmDiff
namespace SoficGroups.KunDiagonalGoodRootGraphLoss
theorem _root_.solution {V : Type*}
    [Fintype V] [DecidableEq V]
    (p : Equiv.Perm V) (B : Finset V) :
    (Fintype.card V : ℝ) - 2 * (B.card : ℝ) ≤
      ((goodPermutationGraph p B).card : ℝ) := by
  have hloss :
      (((SoficGroups.permutationGraph p \
        goodPermutationGraph p B).card : ℕ) : ℝ) ≤
          2 * (B.card : ℝ) := by
    exact_mod_cast card_permutationGraph_sdiff_goodPermutationGraph_le p B
  have htotal :
      (((SoficGroups.permutationGraph p \
        goodPermutationGraph p B).card : ℕ) : ℝ) +
          ((goodPermutationGraph p B).card : ℝ) =
        (Fintype.card V : ℝ) := by
    exact_mod_cast card_goodPermutationGraph_add_graph_loss p B
  linarith
end SoficGroups.KunDiagonalGoodRootGraphLoss
