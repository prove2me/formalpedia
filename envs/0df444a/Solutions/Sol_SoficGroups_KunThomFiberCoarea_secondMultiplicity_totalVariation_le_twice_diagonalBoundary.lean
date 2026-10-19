-- Prove2me | solution 1 for SoficGroups.KunThomFiberCoarea.secondMultiplicity_totalVariation_le_twice_diagonalBoundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.294654+00:00
-- url     : https://prove2.me/submissions/8ab6b1f3-55a4-4d8e-82d8-6dfd630a67cf

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunThomFiberCoarea_secondMultiplicity_diagonal_variation_le_twice_exit

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunThomFiberCoarea
namespace SoficGroups.KunThomFiberCoarea
theorem _root_.solution
    {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (U : Finset (V × V)) :
    (∑ i : ι, ∑ x : V,
      Nat.dist (secondMultiplicity U (σ i x))
        (secondMultiplicity U x)) ≤
          2 * SoficGroups.boundary
            (fun i => (σ i).prodCongr (σ i)) U := by
  classical
  calc
    (∑ i : ι, ∑ x : V,
      Nat.dist (secondMultiplicity U (σ i x))
        (secondMultiplicity U x)) ≤
        ∑ i : ι, 2 * diagonalExit (σ i) U := by
          apply Finset.sum_le_sum
          intro i _
          exact secondMultiplicity_diagonal_variation_le_twice_exit
            (σ i) U
    _ = 2 * SoficGroups.boundary
          (fun i => (σ i).prodCongr (σ i)) U := by
          simp [diagonalExit, SoficGroups.boundary, Finset.mul_sum]
end SoficGroups.KunThomFiberCoarea
