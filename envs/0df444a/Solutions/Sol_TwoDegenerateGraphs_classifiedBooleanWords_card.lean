-- Prove2me | solution 1 for TwoDegenerateGraphs.classifiedBooleanWords_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:06.124263+00:00
-- url     : https://prove2.me/submissions/54fb33c3-53d0-43f7-94fa-9c97f55e570e

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_booleanWordsOfWeight_card

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution
    {ι γ : Type*} [Fintype ι] [Fintype γ] [DecidableEq γ]
    (classify : ι → γ) (counts : γ → ℕ) :
    (classifiedBooleanWords classify counts).card =
      ∏ group : γ,
        (Fintype.card (ClassificationFiber classify group)).choose
          (counts group) := by
  calc
    (classifiedBooleanWords classify counts).card =
        Fintype.card ↥(classifiedBooleanWords classify counts) :=
      (Fintype.card_coe _).symm
    _ = Fintype.card
        (∀ group : γ,
          ↥(booleanWordsOfWeight
            (ClassificationFiber classify group) (counts group))) :=
      Fintype.card_congr (classifiedBooleanWordsEquiv classify counts)
    _ = ∏ group : γ,
          Fintype.card
            ↥(booleanWordsOfWeight
              (ClassificationFiber classify group) (counts group)) := by
      rw [Fintype.card_pi]
    _ = ∏ group : γ,
          (Fintype.card (ClassificationFiber classify group)).choose
            (counts group) := by
      apply Finset.prod_congr rfl
      intro group _
      rw [Fintype.card_coe,
        booleanWordsOfWeight_card]
end TwoDegenerateGraphs
