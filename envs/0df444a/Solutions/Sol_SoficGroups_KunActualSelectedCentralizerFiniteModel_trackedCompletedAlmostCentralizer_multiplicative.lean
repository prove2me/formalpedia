-- Prove2me | solution 1 for SoficGroups.KunActualSelectedCentralizerFiniteModel.trackedCompletedAlmostCentralizer_multiplicative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:01.668904+00:00
-- url     : https://prove2.me/submissions/2c2e2ac9-5868-4cb7-98c6-e5bcec04e3c1

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_CompressionCriterion_mem_productTrackedTable
import Theorems.Thm_SoficGroups_CompressionCriterion_mul_mem_productTrackedTable
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
    (hmul : ∀ x ∈ F, ∀ y ∈ F,
      5 * SoficGroups.permutationDistance
        (p (x * y)) (p x * p y) ≤ Fintype.card V) :
    ∀ x ∈ F, ∀ y ∈ F,
      5 * SoficGroups.permutationDistance
        (trackedCompletedAlmostCentralizer
          σ p F t hdefect (x * y)).permutation
        ((trackedCompletedAlmostCentralizer
          σ p F t hdefect x).permutation *
         (trackedCompletedAlmostCentralizer
          σ p F t hdefect y).permutation) ≤ Fintype.card V := by
  intro x hx y hy
  rw [trackedCompletedAlmostCentralizer_permutation_of_mem
    σ p F t hdefect
      (SoficGroups.CompressionCriterion.mul_mem_productTrackedTable hx hy),
    trackedCompletedAlmostCentralizer_permutation_of_mem
      σ p F t hdefect
        (SoficGroups.CompressionCriterion.mem_productTrackedTable hx),
    trackedCompletedAlmostCentralizer_permutation_of_mem
      σ p F t hdefect
        (SoficGroups.CompressionCriterion.mem_productTrackedTable hy)]
  exact hmul x hx y hy
end SoficGroups.KunActualSelectedCentralizerFiniteModel
