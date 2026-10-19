-- Prove2me | solution 1 for SoficGroups.partitionWordCrossing_indexed_sum_card_le_target_add_unmatched
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.013021+00:00
-- url     : https://prove2.me/submissions/d2b0045b-08bc-47f1-9d9a-ba66ab69341c

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_partitionWordCrossing_card_le_target_add_unmatched

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution
    {V ι : Type*} [DecidableEq V] {U : Finset V}
    (P Q : Finpartition U) (R : Finset (Finset V))
    (hR : R ⊆ P.parts) (D : Finset V → Finset V)
    (hD : ∀ C ∈ R, D C ∈ Q.parts)
    (hinj : Set.InjOn D (R : Set (Finset V)))
    (I : Finset ι) (w : ι → Equiv.Perm V) :
    (∑ i ∈ I, (partitionWordCrossing P (w i)).card) ≤
      (∑ i ∈ I, (partitionWordCrossing Q (w i)).card) +
        2 * I.card * (U \ matchedCore R D).card := by
  calc
    (∑ i ∈ I, (partitionWordCrossing P (w i)).card) ≤
        ∑ i ∈ I,
          ((partitionWordCrossing Q (w i)).card +
            2 * (U \ matchedCore R D).card) :=
      Finset.sum_le_sum fun i _ =>
        partitionWordCrossing_card_le_target_add_unmatched
          P Q R hR D hD hinj (w i)
    _ = (∑ i ∈ I, (partitionWordCrossing Q (w i)).card) +
          2 * I.card * (U \ matchedCore R D).card := by
      simp [Finset.sum_add_distrib, mul_comm, mul_assoc]
end SoficGroups
