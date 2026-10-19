-- Prove2me | solution 1 for SoficGroups.KunActualSelectedCentralizerFiniteModel.trackedCompletedAlmostCentralizer_separated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:01.668904+00:00
-- url     : https://prove2.me/submissions/d2287413-05af-4a6a-ae97-3df7ba80f8d8

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_CompressionCriterion_mem_productTrackedTable
import Theorems.Thm_SoficGroups_KunActualSelectedCentralizerFiniteModel_trackedCompletedAlmostCentralizer_permutation_of_mem

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunActualSelectedCentralizerFiniteModel
open Filter Topology
namespace SoficGroups.KunActualSelectedCentralizerFiniteModel
theorem _root_.solution
    {V ι J : Type} [Fintype V] [DecidableEq V]
    [Fintype ι] [Group J]
    (σ : ι → Equiv.Perm V)
    (p : J → Equiv.Perm V)
    (F : Finset J) (t : ℕ)
    (hdefect : ∀ j ∈ SoficGroups.CompressionCriterion.productTrackedTable F,
      SoficGroups.permutationCommutationDefect σ (p j) ≤ t)
    (hsep : ∀ x ∈ F, ∀ y ∈ F, x ≠ y →
      Fintype.card V < 5 * SoficGroups.permutationDistance (p x) (p y)) :
    ∀ x ∈ F, ∀ y ∈ F, x ≠ y →
      Fintype.card V <
        5 * SoficGroups.permutationDistance
          (trackedCompletedAlmostCentralizer
            σ p F t hdefect x).permutation
          (trackedCompletedAlmostCentralizer
            σ p F t hdefect y).permutation := by
  intro x hx y hy hxy
  rw [trackedCompletedAlmostCentralizer_permutation_of_mem
    σ p F t hdefect
      (SoficGroups.CompressionCriterion.mem_productTrackedTable hx),
    trackedCompletedAlmostCentralizer_permutation_of_mem
      σ p F t hdefect
        (SoficGroups.CompressionCriterion.mem_productTrackedTable hy)]
  exact hsep x hx y hy hxy
end SoficGroups.KunActualSelectedCentralizerFiniteModel
