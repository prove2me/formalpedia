-- Prove2me | solution 1 for SoficGroups.KunThomFiberCoarea.firstMultiplicity_totalVariation_le_twice_diagonalBoundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.294654+00:00
-- url     : https://prove2.me/submissions/160650cc-bdf0-4115-927b-3442f740c9b7

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunThomFiberCoarea_firstMultiplicity_diagonal_variation_le_twice_exit

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunThomFiberCoarea
namespace SoficGroups.KunThomFiberCoarea
theorem _root_.solution
    {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (U : Finset (V × V)) :
    (∑ i : ι, ∑ x : V,
      Nat.dist (firstMultiplicity U (σ i x))
        (firstMultiplicity U x)) ≤
          2 * SoficGroups.boundary
            (fun i => (σ i).prodCongr (σ i)) U := by
  classical
  calc
    (∑ i : ι, ∑ x : V,
      Nat.dist (firstMultiplicity U (σ i x))
        (firstMultiplicity U x)) ≤
        ∑ i : ι, 2 * diagonalExit (σ i) U := by
          apply Finset.sum_le_sum
          intro i _
          exact firstMultiplicity_diagonal_variation_le_twice_exit
            (σ i) U
    _ = 2 * SoficGroups.boundary
          (fun i => (σ i).prodCongr (σ i)) U := by
          simp [diagonalExit, SoficGroups.boundary, Finset.mul_sum]
end SoficGroups.KunThomFiberCoarea
