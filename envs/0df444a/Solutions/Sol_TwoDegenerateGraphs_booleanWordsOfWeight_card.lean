-- Prove2me | solution 1 for TwoDegenerateGraphs.booleanWordsOfWeight_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:06.124263+00:00
-- url     : https://prove2.me/submissions/abdc582b-d7bb-4644-a912-9cf3df8033f0

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution
    (ι : Type*) [Fintype ι] (weight : ℕ) :
    (booleanWordsOfWeight ι weight).card =
      (Fintype.card ι).choose weight := by
  calc
    (booleanWordsOfWeight ι weight).card =
        Fintype.card ↥(booleanWordsOfWeight ι weight) :=
      (Fintype.card_coe _).symm
    _ = Fintype.card
        ↥((Finset.univ : Finset ι).powersetCard weight) :=
      Fintype.card_congr (booleanWordsOfWeightEquiv ι weight)
    _ = ((Finset.univ : Finset ι).powersetCard weight).card :=
      Fintype.card_coe _
    _ = (Fintype.card ι).choose weight := by
      simp
end TwoDegenerateGraphs
