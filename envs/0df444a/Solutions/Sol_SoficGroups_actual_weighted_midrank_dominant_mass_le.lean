-- Prove2me | solution 1 for SoficGroups.actual_weighted_midrank_dominant_mass_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:52.29415+00:00
-- url     : https://prove2.me/submissions/5bfb18ee-b4c2-4d0c-9c95-ad67677bf354

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_weighted_midrank_dominant_mass_le
import Theorems.Thm_SoficGroups_componentRankMassList_sum
import Theorems.Thm_SoficGroups_componentRankMassList_nonneg
import Theorems.Thm_SoficGroups_componentRankMassList_le_max
import Theorems.Thm_SoficGroups_component_omitted_rank_card_eq

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution
    {V ι : Type*}
    (I : Finset ι) (C : ι → Finset V) (b : V → ℤ) (j : ι → ℤ)
    (hC : ∀ i ∈ I, (C i).Nonempty)
    (hmax : ∀ i ∈ I, ∀ k ∈ (C i).image b,
      componentRankMass (C i) b k ≤ componentRankMass (C i) b (j i)) :
    (∑ i ∈ I,
      (((C i).card - ((C i).filter fun x => b x = j i).card : ℕ) : ℝ)) ≤
      12 * ∑ i ∈ I,
        ((C i).card : ℝ) *
          midrankVariance (componentRankMassList (C i) b) := by
  calc
    (∑ i ∈ I,
        (((C i).card - ((C i).filter fun x => b x = j i).card : ℕ) : ℝ)) =
      ∑ i ∈ I,
        ((C i).card : ℝ) *
          (1 - componentRankMass (C i) b (j i)) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact component_omitted_rank_card_eq (C i) b (j i) (hC i hi)
    _ ≤ 12 * ∑ i ∈ I,
        ((C i).card : ℝ) *
          midrankVariance (componentRankMassList (C i) b) := by
      apply weighted_midrank_dominant_mass_le
        I (fun i => ((C i).card : ℝ))
        (fun i => componentRankMassList (C i) b)
        (fun i => componentRankMass (C i) b (j i))
      · intro i hi
        positivity
      · intro i hi
        exact componentRankMassList_sum (C i) b (hC i hi)
      · intro i hi
        exact componentRankMassList_nonneg (C i) b
      · intro i hi
        exact componentRankMassList_le_max (C i) b (j i) (hmax i hi)
end SoficGroups
