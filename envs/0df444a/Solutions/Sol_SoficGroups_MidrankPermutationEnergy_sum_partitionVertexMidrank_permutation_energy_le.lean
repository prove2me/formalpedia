-- Prove2me | solution 1 for SoficGroups.MidrankPermutationEnergy.sum_partitionVertexMidrank_permutation_energy_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.013021+00:00
-- url     : https://prove2.me/submissions/57377fef-8dde-4636-a5ce-013a50669fe3

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_MidrankPermutationEnergy_partitionVertexMidrank_permutation_energy_le

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
open SoficGroups.MidrankPermutationEnergy
namespace SoficGroups.MidrankPermutationEnergy
theorem _root_.solution
    {V ι : Type*} [Fintype V] [DecidableEq V]
    (I : Finset ι)
    (P : Finpartition (Finset.univ : Finset V))
    (b : V → ℤ) (p : ι → Equiv.Perm V) :
    (∑ i ∈ I, ∑ x : V,
      (partitionVertexMidrank P b (p i x) -
        partitionVertexMidrank P b x) ^ 2) ≤
      2 * (∑ i ∈ I, ((partitionWordCrossing P (p i)).card : ℝ)) +
        2 * (∑ i ∈ I,
          ((rankDecreasingVertices Finset.univ b (p i)).card : ℝ)) := by
  calc
    (∑ i ∈ I, ∑ x : V,
        (partitionVertexMidrank P b (p i x) -
          partitionVertexMidrank P b x) ^ 2) ≤
      ∑ i ∈ I,
        (2 * ((partitionWordCrossing P (p i)).card : ℝ) +
          2 * ((rankDecreasingVertices Finset.univ b (p i)).card : ℝ)) := by
            apply Finset.sum_le_sum
            intro i hi
            exact partitionVertexMidrank_permutation_energy_le P b (p i)
    _ = 2 * (∑ i ∈ I, ((partitionWordCrossing P (p i)).card : ℝ)) +
          2 * (∑ i ∈ I,
            ((rankDecreasingVertices Finset.univ b (p i)).card : ℝ)) := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
end SoficGroups.MidrankPermutationEnergy
