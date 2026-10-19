-- Prove2me | solution 1 for SoficGroups.KunThomFiberCoarea.card_nonSingletonFirstMultiplicity_le_reference_difference
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.923416+00:00
-- url     : https://prove2.me/submissions/3891de50-f22f-4e83-a0ab-ae4f99ed371f

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunThomFiberCoarea_firstMultiplicity_variation_le_relation_difference
import Theorems.Thm_SoficGroups_KunThomFiberCoarea_firstMultiplicity_permutationGraph
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
      firstMultiplicity U x ≠ 1).card ≤
        (U \ SoficGroups.permutationGraph p).card +
          (SoficGroups.permutationGraph p \ U).card := by
  have hcount := card_nonSingletonMultiplicity_le_total_distance
    (firstMultiplicity U)
  have hvariation := firstMultiplicity_variation_le_relation_difference
    U (SoficGroups.permutationGraph p)
  simp_rw [firstMultiplicity_permutationGraph] at hvariation
  exact hcount.trans hvariation
end SoficGroups.KunThomFiberCoarea
