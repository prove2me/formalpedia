-- Prove2me | solution 1 for SoficGroups.KunThomFiberCoarea.secondMultiplicity_diagonal_variation_le_twice_exit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.294654+00:00
-- url     : https://prove2.me/submissions/80ce29d4-ad92-4782-92f0-e1c1b8c1ea6e

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunThomFiberCoarea_secondMultiplicity_variation_le_relation_difference
import Theorems.Thm_SoficGroups_KunThomFiberCoarea_secondMultiplicity_diagonalImage
import Theorems.Thm_SoficGroups_KunThomFiberCoarea_diagonalImage_sdiff_cards

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunThomFiberCoarea
namespace SoficGroups.KunThomFiberCoarea
theorem _root_.solution
    {V : Type*} [Fintype V] [DecidableEq V]
    (p : Equiv.Perm V) (U : Finset (V × V)) :
    (∑ x : V, Nat.dist (secondMultiplicity U (p x))
      (secondMultiplicity U x)) ≤ 2 * diagonalExit p U := by
  classical
  calc
    (∑ x : V, Nat.dist (secondMultiplicity U (p x))
      (secondMultiplicity U x)) =
        ∑ x : V, Nat.dist (secondMultiplicity U (p x))
          (secondMultiplicity (diagonalImage p U) (p x)) := by
          apply Finset.sum_congr rfl
          intro x _
          rw [secondMultiplicity_diagonalImage]
    _ = ∑ x : V, Nat.dist (secondMultiplicity U x)
          (secondMultiplicity (diagonalImage p U) x) :=
          Equiv.sum_comp p (fun x =>
            Nat.dist (secondMultiplicity U x)
              (secondMultiplicity (diagonalImage p U) x))
    _ ≤ (U \ diagonalImage p U).card +
          (diagonalImage p U \ U).card :=
          secondMultiplicity_variation_le_relation_difference
            U (diagonalImage p U)
    _ = 2 * diagonalExit p U := by
          obtain ⟨hforward, hbackward⟩ := diagonalImage_sdiff_cards p U
          rw [hforward, hbackward]
          omega
end SoficGroups.KunThomFiberCoarea
