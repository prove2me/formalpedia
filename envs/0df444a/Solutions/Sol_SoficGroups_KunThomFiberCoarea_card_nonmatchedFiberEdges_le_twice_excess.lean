-- Prove2me | solution 1 for SoficGroups.KunThomFiberCoarea.card_nonmatchedFiberEdges_le_twice_excess
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.923416+00:00
-- url     : https://prove2.me/submissions/b9a40e1b-d021-4334-b91a-3c8930d62225

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunThomFiberCoarea_card_nonSingletonFirstEdges_le_twice_excess
import Theorems.Thm_SoficGroups_KunThomFiberCoarea_card_nonSingletonSecondEdges_le_twice_excess
import Theorems.Thm_SoficGroups_KunThomFiberCoarea_nonmatchedFiberEdges_subset

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunThomFiberCoarea
namespace SoficGroups.KunThomFiberCoarea
theorem _root_.solution
    {V : Type*} [Fintype V] [DecidableEq V]
    (U : Finset (V × V)) :
    (U \ matchedFiberEdges U).card ≤
      2 * (∑ x : V, (firstMultiplicity U x - 1 : ℕ)) +
        2 * (∑ x : V, (secondMultiplicity U x - 1 : ℕ)) := by
  calc
    (U \ matchedFiberEdges U).card ≤
        (nonSingletonFirstEdges U ∪ nonSingletonSecondEdges U).card :=
      Finset.card_le_card (nonmatchedFiberEdges_subset U)
    _ ≤ (nonSingletonFirstEdges U).card +
          (nonSingletonSecondEdges U).card :=
      Finset.card_union_le _ _
    _ ≤ 2 * (∑ x : V, (firstMultiplicity U x - 1 : ℕ)) +
          2 * (∑ x : V, (secondMultiplicity U x - 1 : ℕ)) :=
      Nat.add_le_add
        (card_nonSingletonFirstEdges_le_twice_excess U)
        (card_nonSingletonSecondEdges_le_twice_excess U)
end SoficGroups.KunThomFiberCoarea
