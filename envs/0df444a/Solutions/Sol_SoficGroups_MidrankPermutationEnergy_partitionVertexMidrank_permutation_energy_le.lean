-- Prove2me | solution 1 for SoficGroups.MidrankPermutationEnergy.partitionVertexMidrank_permutation_energy_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.013021+00:00
-- url     : https://prove2.me/submissions/49710c85-0019-4c4e-92c7-a19e759fd92f

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_permutation_squared_increment_le_twice_decreasing
import Theorems.Thm_SoficGroups_componentVertexMidrank_nonneg
import Theorems.Thm_SoficGroups_componentVertexMidrank_le_one
import Theorems.Thm_SoficGroups_MidrankPermutationEnergy_midpointDecreasing_subset_crossing_union_rankDecreasing

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
open SoficGroups.MidrankPermutationEnergy
namespace SoficGroups.MidrankPermutationEnergy
theorem _root_.solution
    {V : Type*} [Fintype V] [DecidableEq V]
    (P : Finpartition (Finset.univ : Finset V))
    (b : V → ℤ) (p : Equiv.Perm V) :
    (∑ x : V,
      (partitionVertexMidrank P b (p x) -
        partitionVertexMidrank P b x) ^ 2) ≤
      2 * ((partitionWordCrossing P p).card : ℝ) +
        2 * ((rankDecreasingVertices Finset.univ b p).card : ℝ) := by
  have hbase := SoficGroups.permutation_squared_increment_le_twice_decreasing
    p (partitionVertexMidrank P b)
    (fun x => componentVertexMidrank_nonneg (P.part x) b x)
    (fun x => componentVertexMidrank_le_one (P.part x) b x)
  have hsubset :
      (Finset.univ.filter fun x =>
        partitionVertexMidrank P b (p x) < partitionVertexMidrank P b x) ⊆
        partitionWordCrossing P p ∪
          rankDecreasingVertices Finset.univ b p := by
    exact midpointDecreasing_subset_crossing_union_rankDecreasing P b p
  have hcard :
      (Finset.univ.filter fun x =>
        partitionVertexMidrank P b (p x) <
          partitionVertexMidrank P b x).card ≤
        (partitionWordCrossing P p).card +
          (rankDecreasingVertices Finset.univ b p).card :=
    (Finset.card_le_card hsubset).trans
      (Finset.card_union_le _ _)
  have hcast :
      ((Finset.univ.filter fun x =>
        partitionVertexMidrank P b (p x) <
          partitionVertexMidrank P b x).card : ℝ) ≤
        ((partitionWordCrossing P p).card : ℝ) +
          ((rankDecreasingVertices Finset.univ b p).card : ℝ) := by
    exact_mod_cast hcard
  nlinarith
end SoficGroups.MidrankPermutationEnergy
