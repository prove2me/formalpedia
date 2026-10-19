-- Prove2me | solution 1 for SoficGroups.KunThomFiberCoarea.unmatched_vertices_le_zero_and_excess
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.923416+00:00
-- url     : https://prove2.me/submissions/d2879fa0-6699-4435-9fa9-6bacbd2d0d3a

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunThomFiberCoarea_card_singletonSupport_le_matching_add_column_excess
import Theorems.Thm_SoficGroups_KunThomFiberCoarea_card_le_zero_singleton_excess

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunThomFiberCoarea
namespace SoficGroups.KunThomFiberCoarea
theorem _root_.solution
    {V : Type*} [Fintype V] [DecidableEq V]
    (U : Finset (V × V)) :
    Fintype.card V - (matchedFiberEdges U).card ≤
      (Finset.univ.filter fun x : V => firstMultiplicity U x = 0).card +
        (∑ x : V, (firstMultiplicity U x - 1 : ℕ)) +
        2 * (∑ x : V, (secondMultiplicity U x - 1 : ℕ)) := by
  have hpopulation := card_le_zero_singleton_excess
    (firstMultiplicity U)
  have hsingle := card_singletonSupport_le_matching_add_column_excess U
  omega
end SoficGroups.KunThomFiberCoarea
