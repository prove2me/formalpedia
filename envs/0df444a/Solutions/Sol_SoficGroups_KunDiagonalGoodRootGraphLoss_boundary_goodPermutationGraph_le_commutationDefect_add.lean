-- Prove2me | solution 1 for SoficGroups.KunDiagonalGoodRootGraphLoss.boundary_goodPermutationGraph_le_commutationDefect_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:58.258203+00:00
-- url     : https://prove2.me/submissions/af7b0c49-2bf7-4f83-a77d-be8b5fde7948

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_boundary_permutationGraph_eq_commutationDefect
import Theorems.Thm_SoficGroups_KunThomFiberCoarea_boundary_le_boundary_add_sdiff
import Theorems.Thm_SoficGroups_KunDiagonalGoodRootGraphLoss_goodPermutationGraph_subset
import Theorems.Thm_SoficGroups_KunDiagonalGoodRootGraphLoss_card_permutationGraph_sdiff_goodPermutationGraph_le

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunDiagonalGoodRootGraphLoss
open scoped BigOperators symmDiff
namespace SoficGroups.KunDiagonalGoodRootGraphLoss
theorem _root_.solution {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (p : Equiv.Perm V) (B : Finset V) :
    SoficGroups.boundary
        (fun i => (σ i).prodCongr (σ i)) (goodPermutationGraph p B) ≤
      SoficGroups.permutationCommutationDefect σ p +
        2 * Fintype.card ι * B.card := by
  have hboundary :=
    SoficGroups.KunThomFiberCoarea.boundary_le_boundary_add_sdiff
      (fun i => (σ i).prodCongr (σ i))
      (goodPermutationGraph p B) (SoficGroups.permutationGraph p)
  rw [SoficGroups.boundary_permutationGraph_eq_commutationDefect,
    Finset.sdiff_eq_empty_iff_subset.mpr
      (goodPermutationGraph_subset p B),
    Finset.card_empty, zero_add] at hboundary
  calc
    SoficGroups.boundary
        (fun i => (σ i).prodCongr (σ i)) (goodPermutationGraph p B) ≤
      SoficGroups.permutationCommutationDefect σ p +
        Fintype.card ι *
          (SoficGroups.permutationGraph p \
            goodPermutationGraph p B).card := hboundary
    _ ≤ SoficGroups.permutationCommutationDefect σ p +
        Fintype.card ι * (2 * B.card) := by
      gcongr
      exact card_permutationGraph_sdiff_goodPermutationGraph_le p B
    _ = SoficGroups.permutationCommutationDefect σ p +
        2 * Fintype.card ι * B.card := by
      ring
end SoficGroups.KunDiagonalGoodRootGraphLoss
