-- Prove2me | solution 1 for SoficGroups.KunThomFiberCoarea.firstMultiplicity_diagonal_variation_le_twice_exit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.294654+00:00
-- url     : https://prove2.me/submissions/e2230f69-0588-4ba9-a680-7f6a94951839

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunThomFiberCoarea_firstMultiplicity_variation_le_relation_difference
import Theorems.Thm_SoficGroups_KunThomFiberCoarea_firstMultiplicity_diagonalImage
import Theorems.Thm_SoficGroups_KunThomFiberCoarea_diagonalImage_sdiff_cards

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunThomFiberCoarea
namespace SoficGroups.KunThomFiberCoarea
theorem _root_.solution
    {V : Type*} [Fintype V] [DecidableEq V]
    (p : Equiv.Perm V) (U : Finset (V × V)) :
    (∑ x : V, Nat.dist (firstMultiplicity U (p x))
      (firstMultiplicity U x)) ≤ 2 * diagonalExit p U := by
  classical
  calc
    (∑ x : V, Nat.dist (firstMultiplicity U (p x))
      (firstMultiplicity U x)) =
        ∑ x : V, Nat.dist (firstMultiplicity U (p x))
          (firstMultiplicity (diagonalImage p U) (p x)) := by
          apply Finset.sum_congr rfl
          intro x _
          rw [firstMultiplicity_diagonalImage]
    _ = ∑ x : V, Nat.dist (firstMultiplicity U x)
          (firstMultiplicity (diagonalImage p U) x) :=
          Equiv.sum_comp p (fun x =>
            Nat.dist (firstMultiplicity U x)
              (firstMultiplicity (diagonalImage p U) x))
    _ ≤ (U \ diagonalImage p U).card +
          (diagonalImage p U \ U).card :=
          firstMultiplicity_variation_le_relation_difference
            U (diagonalImage p U)
    _ = 2 * diagonalExit p U := by
          obtain ⟨hforward, hbackward⟩ := diagonalImage_sdiff_cards p U
          rw [hforward, hbackward]
          omega
end SoficGroups.KunThomFiberCoarea
