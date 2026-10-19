-- Prove2me | solution 1 for SoficGroups.KunPositiveWordMidrankEnergy.sofic_action_squared_energy_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.855273+00:00
-- url     : https://prove2.me/submissions/64813d3e-1be9-4a86-bf25-de24f4c6f3d5

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunPositiveWordMidrankEnergy_squaredPermutationEnergy_tendsto_of_normalizedHamming
import Theorems.Thm_SoficGroups_KunPositiveWordMidrankEnergy_squaredPermutationEnergy_mul_tendsto_zero

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunPositiveWordMidrankEnergy
open Filter Topology
open scoped BigOperators
namespace SoficGroups.KunPositiveWordMidrankEnergy
theorem _root_.solution
    {G : Type*} [Group G]
    (A : SoficGroups.SoficApproximation G)
    (f : (n : ℕ) → Fin (A.model n).size → ℝ)
    (hf0 : ∀ n x, 0 ≤ f n x)
    (hf1 : ∀ n x, f n x ≤ 1)
    (g h : G)
    (hg : Tendsto
      (fun n =>
        squaredPermutationEnergy (f n) ((A.model n).action g) /
          (A.model n).size) atTop (𝓝 0))
    (hh : Tendsto
      (fun n =>
        squaredPermutationEnergy (f n) ((A.model n).action h) /
          (A.model n).size) atTop (𝓝 0)) :
    Tendsto
      (fun n =>
        squaredPermutationEnergy (f n) ((A.model n).action (g * h)) /
          (A.model n).size) atTop (𝓝 0) := by
  have hproduct : Tendsto
      (fun n =>
        squaredPermutationEnergy (f n)
          ((A.model n).action g * (A.model n).action h) /
          (A.model n).size) atTop (𝓝 0) := by
    simpa only [Fintype.card_fin] using
      (squaredPermutationEnergy_mul_tendsto_zero
        (fun n => Fin (A.model n).size) f
        (fun n => (A.model n).action g)
        (fun n => (A.model n).action h)
        (by simpa only [Fintype.card_fin] using hg)
        (by simpa only [Fintype.card_fin] using hh))
  simpa only [Fintype.card_fin] using
    (squaredPermutationEnergy_tendsto_of_normalizedHamming
      (fun n => Fin (A.model n).size) f hf0 hf1
      (fun n => (A.model n).action (g * h))
      (fun n => (A.model n).action g * (A.model n).action h)
      (by simpa only [Fintype.card_fin] using hproduct)
      (A.multiplicative g h))
end SoficGroups.KunPositiveWordMidrankEnergy
