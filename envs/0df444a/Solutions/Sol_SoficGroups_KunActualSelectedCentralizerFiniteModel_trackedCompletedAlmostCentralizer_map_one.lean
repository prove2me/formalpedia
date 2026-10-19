-- Prove2me | solution 1 for SoficGroups.KunActualSelectedCentralizerFiniteModel.trackedCompletedAlmostCentralizer_map_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.855273+00:00
-- url     : https://prove2.me/submissions/6b356849-667c-4f50-8fa1-125a17c8eb09

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_CompressionCriterion_one_mem_productTrackedTable
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
    (hp : p 1 = 1)
    (F : Finset J) (t : ℕ)
    (hdefect : ∀ j ∈ SoficGroups.CompressionCriterion.productTrackedTable F,
      SoficGroups.permutationCommutationDefect σ (p j) ≤ t) :
    (trackedCompletedAlmostCentralizer σ p F t hdefect 1).permutation = 1 := by
  rw [trackedCompletedAlmostCentralizer_permutation_of_mem
    σ p F t hdefect
      (SoficGroups.CompressionCriterion.one_mem_productTrackedTable F), hp]
end SoficGroups.KunActualSelectedCentralizerFiniteModel
