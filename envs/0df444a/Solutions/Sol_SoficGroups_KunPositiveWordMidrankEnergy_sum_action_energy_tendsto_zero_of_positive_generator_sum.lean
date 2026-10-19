-- Prove2me | solution 1 for SoficGroups.KunPositiveWordMidrankEnergy.sum_action_energy_tendsto_zero_of_positive_generator_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.855273+00:00
-- url     : https://prove2.me/submissions/f08dc19d-ff2e-424a-8431-da2d6e17c0a2

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunPositiveWordMidrankEnergy_action_energy_tendsto_zero_of_positive_generator_sum

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunPositiveWordMidrankEnergy
open Filter Topology
open scoped BigOperators
namespace SoficGroups.KunPositiveWordMidrankEnergy
theorem _root_.solution
    {G ι : Type*} [Group G] [Fintype ι]
    (A : SoficGroups.SoficApproximation G)
    (s : ι → G)
    (hgenerate : Subgroup.closure (Set.range s) = ⊤)
    (f : (n : ℕ) → Fin (A.model n).size → ℝ)
    (hf0 : ∀ n x, 0 ≤ f n x)
    (hf1 : ∀ n x, f n x ≤ 1)
    (hpositive : Tendsto
      (fun n =>
        (∑ i : ι,
          squaredPermutationEnergy (f n)
            ((A.model n).action (s i))) /
          (A.model n).size) atTop (𝓝 0))
    (S : Finset G) :
    Tendsto
      (fun n =>
        (∑ g ∈ S,
          squaredPermutationEnergy (f n) ((A.model n).action g)) /
          (A.model n).size) atTop (𝓝 0) := by
  have hall := action_energy_tendsto_zero_of_positive_generator_sum
    A s hgenerate f hf0 hf1 hpositive
  have hsum : Tendsto
      (fun n =>
        ∑ g ∈ S,
          squaredPermutationEnergy (f n) ((A.model n).action g) /
            (A.model n).size) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum S (fun g _ => hall g)
  simpa only [Finset.sum_div] using hsum
end SoficGroups.KunPositiveWordMidrankEnergy
