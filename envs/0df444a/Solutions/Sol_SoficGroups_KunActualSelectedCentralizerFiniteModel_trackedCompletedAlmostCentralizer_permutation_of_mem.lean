-- Prove2me | solution 1 for SoficGroups.KunActualSelectedCentralizerFiniteModel.trackedCompletedAlmostCentralizer_permutation_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.855273+00:00
-- url     : https://prove2.me/submissions/94c23e9c-66a9-449b-acb8-d10c21d19136

import Mathlib
import Definitions.Def_NonSoficGroup

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
    {j : J}
    (hj : j ∈ SoficGroups.CompressionCriterion.productTrackedTable F) :
    (trackedCompletedAlmostCentralizer σ p F t hdefect j).permutation =
      p j := by
  classical
  simp [trackedCompletedAlmostCentralizer, hj]
end SoficGroups.KunActualSelectedCentralizerFiniteModel
