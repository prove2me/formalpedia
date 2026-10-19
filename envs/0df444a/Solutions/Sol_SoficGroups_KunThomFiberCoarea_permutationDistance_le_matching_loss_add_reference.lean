-- Prove2me | solution 1 for SoficGroups.KunThomFiberCoarea.permutationDistance_le_matching_loss_add_reference
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.923416+00:00
-- url     : https://prove2.me/submissions/864ce6c0-ef95-4d04-a997-a6e0fd1cd317

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunThomFiberCoarea_permutationGraph_sdiff_bounds_of_matchedFiberEdges
import Theorems.Thm_SoficGroups_KunThomFiberCoarea_permutationDistance_eq_card_permutationGraph_sdiff

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunThomFiberCoarea
namespace SoficGroups.KunThomFiberCoarea
theorem _root_.solution
    {V : Type*} [Fintype V] [DecidableEq V]
    (U : Finset (V × V)) (q p : Equiv.Perm V)
    (hq : matchedFiberEdges U ⊆ SoficGroups.permutationGraph q) :
    SoficGroups.permutationDistance q p ≤
      Fintype.card V - (matchedFiberEdges U).card +
        (U \ SoficGroups.permutationGraph p).card := by
  classical
  obtain ⟨hleft, _⟩ :=
    permutationGraph_sdiff_bounds_of_matchedFiberEdges U q hq
  have hsub :
      SoficGroups.permutationGraph q \
          SoficGroups.permutationGraph p ⊆
        (SoficGroups.permutationGraph q \ U) ∪
          (U \ SoficGroups.permutationGraph p) := by
    intro z hz
    obtain ⟨hzq, hznot⟩ := Finset.mem_sdiff.mp hz
    by_cases hzU : z ∈ U
    · apply Finset.mem_union_right
      exact Finset.mem_sdiff.mpr ⟨hzU, hznot⟩
    · apply Finset.mem_union_left
      exact Finset.mem_sdiff.mpr ⟨hzq, hzU⟩
  rw [permutationDistance_eq_card_permutationGraph_sdiff]
  calc
    (SoficGroups.permutationGraph q \
      SoficGroups.permutationGraph p).card ≤
        ((SoficGroups.permutationGraph q \ U) ∪
          (U \ SoficGroups.permutationGraph p)).card :=
      Finset.card_le_card hsub
    _ ≤ (SoficGroups.permutationGraph q \ U).card +
          (U \ SoficGroups.permutationGraph p).card :=
      Finset.card_union_le _ _
    _ ≤ Fintype.card V - (matchedFiberEdges U).card +
          (U \ SoficGroups.permutationGraph p).card :=
      Nat.add_le_add_right hleft _
end SoficGroups.KunThomFiberCoarea
