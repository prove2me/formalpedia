-- Prove2me | solution 1 for SoficGroups.KunThomFiberCoarea.card_singletonSupport_le_matching_add_column_excess
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.923416+00:00
-- url     : https://prove2.me/submissions/a4d85960-5ddf-4281-96ec-d13b9507470b

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunThomFiberCoarea_card_nonSingletonSecondEdges_le_twice_excess
import Theorems.Thm_SoficGroups_KunThomFiberCoarea_card_singletonFirstEdges
import Theorems.Thm_SoficGroups_KunThomFiberCoarea_singletonFirstEdges_subset_matching_union

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunThomFiberCoarea
namespace SoficGroups.KunThomFiberCoarea
theorem _root_.solution
    {V : Type*} [Fintype V] [DecidableEq V]
    (U : Finset (V × V)) :
    (singletonSupport (firstMultiplicity U)).card ≤
      (matchedFiberEdges U).card +
        2 * (∑ x : V, (secondMultiplicity U x - 1 : ℕ)) := by
  rw [← card_singletonFirstEdges U]
  calc
    (singletonFirstEdges U).card ≤
        (matchedFiberEdges U ∪ nonSingletonSecondEdges U).card :=
      Finset.card_le_card (singletonFirstEdges_subset_matching_union U)
    _ ≤ (matchedFiberEdges U).card +
          (nonSingletonSecondEdges U).card :=
      Finset.card_union_le _ _
    _ ≤ (matchedFiberEdges U).card +
          2 * (∑ x : V, (secondMultiplicity U x - 1 : ℕ)) :=
      Nat.add_le_add_left
        (card_nonSingletonSecondEdges_le_twice_excess U) _
end SoficGroups.KunThomFiberCoarea
