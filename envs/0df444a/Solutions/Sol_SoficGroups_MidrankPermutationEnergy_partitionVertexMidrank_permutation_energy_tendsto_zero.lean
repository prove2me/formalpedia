-- Prove2me | solution 1 for SoficGroups.MidrankPermutationEnergy.partitionVertexMidrank_permutation_energy_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.013021+00:00
-- url     : https://prove2.me/submissions/271af07c-d864-4469-81df-3d6f958d9bf3

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_MidrankPermutationEnergy_sum_partitionVertexMidrank_permutation_energy_le

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
open SoficGroups.MidrankPermutationEnergy
namespace SoficGroups.MidrankPermutationEnergy
theorem _root_.solution
    (V ι : ℕ → Type*)
    [∀ n, Fintype (V n)] [∀ n, DecidableEq (V n)]
    [∀ n, Fintype (ι n)]
    (P : (n : ℕ) → Finpartition (Finset.univ : Finset (V n)))
    (b : (n : ℕ) → V n → ℤ)
    (p : (n : ℕ) → ι n → Equiv.Perm (V n))
    (N : ℕ → ℝ)
    (hN : ∀ n, 0 < N n)
    (hcross : Tendsto
      (fun n =>
        (∑ i : ι n, ((partitionWordCrossing (P n) (p n i)).card : ℝ)) /
          N n)
      atTop (nhds 0))
    (hrank : Tendsto
      (fun n =>
        (∑ i : ι n,
          ((rankDecreasingVertices Finset.univ (b n) (p n i)).card : ℝ)) /
            N n)
      atTop (nhds 0)) :
    Tendsto
      (fun n =>
        (∑ i : ι n, ∑ x : V n,
          (partitionVertexMidrank (P n) (b n) (p n i x) -
            partitionVertexMidrank (P n) (b n) x) ^ 2) / N n)
      atTop (nhds 0) := by
  have hnonnegative : ∀ n,
      0 ≤ (∑ i : ι n, ∑ x : V n,
          (partitionVertexMidrank (P n) (b n) (p n i x) -
            partitionVertexMidrank (P n) (b n) x) ^ 2) / N n := by
    intro n
    apply div_nonneg _ (hN n).le
    apply Finset.sum_nonneg
    intro i hi
    exact Finset.sum_nonneg fun x hx => sq_nonneg _
  have hupper : ∀ n,
      (∑ i : ι n, ∑ x : V n,
          (partitionVertexMidrank (P n) (b n) (p n i x) -
            partitionVertexMidrank (P n) (b n) x) ^ 2) / N n ≤
        2 * ((∑ i : ι n,
          ((partitionWordCrossing (P n) (p n i)).card : ℝ)) / N n) +
        2 * ((∑ i : ι n,
          ((rankDecreasingVertices Finset.univ (b n) (p n i)).card : ℝ)) /
            N n) := by
    intro n
    have hfinite := sum_partitionVertexMidrank_permutation_energy_le
      (Finset.univ : Finset (ι n)) (P n) (b n) (p n)
    have hdiv := (div_le_div_iff_of_pos_right (hN n)).2 hfinite
    calc
      (∑ i : ι n, ∑ x : V n,
          (partitionVertexMidrank (P n) (b n) (p n i x) -
            partitionVertexMidrank (P n) (b n) x) ^ 2) / N n ≤
        (2 * (∑ i : ι n,
          ((partitionWordCrossing (P n) (p n i)).card : ℝ)) +
         2 * (∑ i : ι n,
          ((rankDecreasingVertices Finset.univ (b n) (p n i)).card : ℝ))) /
            N n := hdiv
      _ = 2 * ((∑ i : ι n,
          ((partitionWordCrossing (P n) (p n i)).card : ℝ)) / N n) +
        2 * ((∑ i : ι n,
          ((rankDecreasingVertices Finset.univ (b n) (p n i)).card : ℝ)) /
            N n) := by ring
  have hlimit : Tendsto
      (fun n =>
        2 * ((∑ i : ι n,
          ((partitionWordCrossing (P n) (p n i)).card : ℝ)) / N n) +
        2 * ((∑ i : ι n,
          ((rankDecreasingVertices Finset.univ (b n) (p n i)).card : ℝ)) /
            N n))
      atTop (nhds 0) := by
    simpa using
      (Filter.Tendsto.const_mul (2 : ℝ) hcross).add
        (Filter.Tendsto.const_mul (2 : ℝ) hrank)
  exact squeeze_zero'
    (Filter.Eventually.of_forall hnonnegative)
    (Filter.Eventually.of_forall hupper)
    hlimit
end SoficGroups.MidrankPermutationEnergy
