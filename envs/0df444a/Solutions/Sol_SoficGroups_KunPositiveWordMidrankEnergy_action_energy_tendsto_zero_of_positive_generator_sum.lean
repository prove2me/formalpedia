-- Prove2me | solution 1 for SoficGroups.KunPositiveWordMidrankEnergy.action_energy_tendsto_zero_of_positive_generator_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.855273+00:00
-- url     : https://prove2.me/submissions/fe530236-7bb9-40a5-9591-ca068c1eff3f

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunPositiveWordMidrankEnergy_squaredPermutationEnergy_nonneg
import Theorems.Thm_SoficGroups_KunPositiveWordMidrankEnergy_sofic_action_squared_energy_mul
import Theorems.Thm_SoficGroups_KunPositiveWordMidrankEnergy_sofic_action_squared_energy_inv

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
          (A.model n).size) atTop (𝓝 0)) :
    ∀ g : G,
      Tendsto
        (fun n =>
          squaredPermutationEnergy (f n) ((A.model n).action g) /
            (A.model n).size) atTop (𝓝 0) := by
  classical
  have hsingle (i : ι) :
      Tendsto
        (fun n =>
          squaredPermutationEnergy (f n) ((A.model n).action (s i)) /
            (A.model n).size) atTop (𝓝 0) := by
    refine squeeze_zero (fun n =>
      div_nonneg
        (squaredPermutationEnergy_nonneg (f n)
          ((A.model n).action (s i)))
        (Nat.cast_nonneg _)) ?_ hpositive
    intro n
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact Finset.single_le_sum
      (fun j _ => squaredPermutationEnergy_nonneg
        (f n) ((A.model n).action (s j)))
      (Finset.mem_univ i)
  intro g
  have hg : g ∈ Subgroup.closure (Set.range s) := by
    rw [hgenerate]
    exact Subgroup.mem_top g
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact hsingle i
  | one =>
      have heq :
          (fun n =>
            squaredPermutationEnergy (f n) ((A.model n).action 1) /
              (A.model n).size) =
            (fun _ : ℕ => (0 : ℝ)) := by
        funext n
        simp [squaredPermutationEnergy, (A.model n).map_one]
      rw [heq]
      exact tendsto_const_nhds
  | mul x y _ _ hx hy =>
      exact sofic_action_squared_energy_mul A f hf0 hf1 x y hx hy
  | inv x _ hx =>
      exact sofic_action_squared_energy_inv A f hf0 hf1 x hx
end SoficGroups.KunPositiveWordMidrankEnergy
