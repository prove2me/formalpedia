-- Prove2me | solution 1 for SoficGroups.KunThomFiberCoarea.card_nonSingletonSecondMultiplicity_le_reference_difference
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.923416+00:00
-- url     : https://prove2.me/submissions/95d9961b-7996-45b0-a8e3-651c67df7bc1

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunThomFiberCoarea_secondMultiplicity_variation_le_relation_difference
import Theorems.Thm_SoficGroups_KunThomFiberCoarea_secondMultiplicity_permutationGraph
import Theorems.Thm_SoficGroups_KunThomFiberCoarea_card_nonSingletonMultiplicity_le_total_distance

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunThomFiberCoarea
namespace SoficGroups.KunThomFiberCoarea
theorem _root_.solution
    {V : Type*} [Fintype V] [DecidableEq V]
    (U : Finset (V × V)) (p : Equiv.Perm V) :
    (Finset.univ.filter fun x : V =>
      secondMultiplicity U x ≠ 1).card ≤
        (U \ SoficGroups.permutationGraph p).card +
          (SoficGroups.permutationGraph p \ U).card := by
  have hcount := card_nonSingletonMultiplicity_le_total_distance
    (secondMultiplicity U)
  have hvariation := secondMultiplicity_variation_le_relation_difference
    U (SoficGroups.permutationGraph p)
  simp_rw [secondMultiplicity_permutationGraph] at hvariation
  exact hcount.trans hvariation
end SoficGroups.KunThomFiberCoarea
