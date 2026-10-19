-- Prove2me | solution 1 for TwoDegenerateGraphs.pairChildArraysOfProfile_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:06.124263+00:00
-- url     : https://prove2.me/submissions/eea77655-b77c-424c-8760-99ae7a30e37f

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_classifiedBooleanWords_card
import Theorems.Thm_TwoDegenerateGraphs_pairCoordinateClassificationFiber_card

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (profile : PairTypeCountProfile parentCount dimension) :
    (pairChildArraysOfProfile parents profile).card =
      ∏ index : PairBitType × Fin dimension,
        ((pairTypeGroup parents index.2 index.1).card).choose
          (profile index.1 index.2).val := by
  calc
    (pairChildArraysOfProfile parents profile).card =
      Fintype.card ↥(pairChildArraysOfProfile parents profile) :=
        (Fintype.card_coe _).symm
    _ = Fintype.card
      ↥(classifiedBooleanWords
        (pairCoordinateClassification parents)
        (fun index : PairBitType × Fin dimension =>
          (profile index.1 index.2).val)) :=
        Fintype.card_congr
          (pairChildArraysOfProfileEquiv parents profile)
    _ = (classifiedBooleanWords
        (pairCoordinateClassification parents)
        (fun index : PairBitType × Fin dimension =>
          (profile index.1 index.2).val)).card :=
        Fintype.card_coe _
    _ = ∏ index : PairBitType × Fin dimension,
        (Fintype.card
          (ClassificationFiber
            (pairCoordinateClassification parents) index)).choose
          (profile index.1 index.2).val :=
        classifiedBooleanWords_card
          (pairCoordinateClassification parents)
          (fun index : PairBitType × Fin dimension =>
            (profile index.1 index.2).val)
    _ = ∏ index : PairBitType × Fin dimension,
        ((pairTypeGroup parents index.2 index.1).card).choose
          (profile index.1 index.2).val := by
      apply Finset.prod_congr rfl
      rintro ⟨bitType, coordinate⟩ _
      rw [pairCoordinateClassificationFiber_card]
end TwoDegenerateGraphs
