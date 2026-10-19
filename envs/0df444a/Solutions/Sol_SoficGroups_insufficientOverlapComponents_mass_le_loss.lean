-- Prove2me | solution 1 for SoficGroups.insufficientOverlapComponents_mass_le_loss
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.013021+00:00
-- url     : https://prove2.me/submissions/875606a6-8feb-4654-a719-edabd827df68

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_insufficientOverlapComponents_subset

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution
    {V : Type u} [DecidableEq V] {U : Finset V}
    (P Q : Finpartition U) (eta : ℝ) :
    eta * (∑ C ∈ insufficientOverlapComponents P Q eta,
        (C.card : ℝ)) ≤
      ∑ C ∈ P.parts,
        ((C.card : ℝ) - ((C ∩ maximumOverlapPart Q C).card : ℝ)) := by
  classical
  calc
    eta * (∑ C ∈ insufficientOverlapComponents P Q eta,
        (C.card : ℝ)) =
      ∑ C ∈ insufficientOverlapComponents P Q eta,
        eta * (C.card : ℝ) := by
          rw [Finset.mul_sum]
    _ ≤ ∑ C ∈ insufficientOverlapComponents P Q eta,
        ((C.card : ℝ) - ((C ∩ maximumOverlapPart Q C).card : ℝ)) := by
          apply Finset.sum_le_sum
          intro C hC
          have hbad :=
            (Finset.mem_filter.mp
              (show C ∈ P.parts.filter (fun C =>
                ((C ∩ maximumOverlapPart Q C).card : ℝ) <
                  (1 - eta) * (C.card : ℝ)) from hC)).2
          linarith
    _ ≤ ∑ C ∈ P.parts,
        ((C.card : ℝ) - ((C ∩ maximumOverlapPart Q C).card : ℝ)) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
            (insufficientOverlapComponents_subset P Q eta)
          intro C _ _
          exact sub_nonneg.mpr (by
            exact_mod_cast Finset.card_le_card
              (Finset.inter_subset_left :
                C ∩ maximumOverlapPart Q C ⊆ C))
end SoficGroups
