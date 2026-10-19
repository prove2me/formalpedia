-- Prove2me | solution 1 for SoficGroups.SourceGeneratedWordCrossing.generator_crossing_density_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.698756+00:00
-- url     : https://prove2.me/submissions/730e0481-10db-4db4-9dbc-d2747a0595c8

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_SourceGeneratedWordCrossing_sum_generator_crossing_eq_sum_partition_boundary

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.SourceGeneratedWordCrossing
open Filter Topology
open scoped BigOperators
namespace SoficGroups.SourceGeneratedWordCrossing
theorem _root_.solution
    {V : ℕ → Type*}
    [∀ n, Fintype (V n)] [∀ n, DecidableEq (V n)]
    {ι : Type*} [Fintype ι]
    (Q : ∀ n, Finpartition (Finset.univ : Finset (V n)))
    (σ : ∀ n, ι → Equiv.Perm (V n))
    (hboundary : Tendsto
      (fun n =>
        (∑ C ∈ (Q n).parts,
          (SoficGroups.boundary (σ n) C : ℝ)) /
            Fintype.card (V n))
      atTop (nhds 0))
    (i : ι) :
    Tendsto
      (fun n =>
        ((SoficGroups.partitionWordCrossing (Q n)
          (σ n i)).card : ℝ) / Fintype.card (V n))
      atTop (nhds 0) := by
  refine squeeze_zero (fun n => by positivity) ?_ hboundary
  intro n
  have hsingle :
      (SoficGroups.partitionWordCrossing (Q n) (σ n i)).card ≤
        ∑ j : ι,
          (SoficGroups.partitionWordCrossing (Q n) (σ n j)).card := by
    exact Finset.single_le_sum
      (fun j _ => Nat.zero_le
        (SoficGroups.partitionWordCrossing (Q n) (σ n j)).card)
      (Finset.mem_univ i)
  have hsum := sum_generator_crossing_eq_sum_partition_boundary
    (Q n) (σ n)
  have hreal :
      ((SoficGroups.partitionWordCrossing (Q n) (σ n i)).card : ℝ) ≤
        ∑ C ∈ (Q n).parts,
          (SoficGroups.boundary (σ n) C : ℝ) := by
    exact_mod_cast hsingle.trans (le_of_eq hsum)
  exact div_le_div_of_nonneg_right hreal (by positivity)
end SoficGroups.SourceGeneratedWordCrossing
