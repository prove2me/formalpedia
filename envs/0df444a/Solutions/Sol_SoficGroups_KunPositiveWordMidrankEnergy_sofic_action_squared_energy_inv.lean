-- Prove2me | solution 1 for SoficGroups.KunPositiveWordMidrankEnergy.sofic_action_squared_energy_inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.855273+00:00
-- url     : https://prove2.me/submissions/62238cca-9a9f-428b-9dd3-e9929fd72d6a

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_normalizedHamming_comm
import Theorems.Thm_SoficGroups_KunPositiveWordMidrankEnergy_squaredPermutationEnergy_inv
import Theorems.Thm_SoficGroups_KunPositiveWordMidrankEnergy_squaredPermutationEnergy_tendsto_of_normalizedHamming
import Theorems.Thm_SoficGroups_KunPositiveWordMidrankEnergy_sofic_action_inverse_normalizedHamming_tendsto_zero

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
    (g : G)
    (hg : Tendsto
      (fun n =>
        squaredPermutationEnergy (f n) ((A.model n).action g) /
          (A.model n).size) atTop (𝓝 0)) :
    Tendsto
      (fun n =>
        squaredPermutationEnergy (f n) ((A.model n).action (g⁻¹)) /
          (A.model n).size) atTop (𝓝 0) := by
  have htrue : Tendsto
      (fun n =>
        squaredPermutationEnergy (f n) (((A.model n).action g)⁻¹) /
          (A.model n).size) atTop (𝓝 0) := by
    simpa only [squaredPermutationEnergy_inv] using hg
  have hd : Tendsto
      (fun n =>
        SoficGroups.normalizedHamming
          ((A.model n).action (g⁻¹))
          (((A.model n).action g)⁻¹)) atTop (𝓝 0) := by
    have heq :
        (fun n =>
          SoficGroups.normalizedHamming
            ((A.model n).action (g⁻¹))
            (((A.model n).action g)⁻¹)) =
          (fun n =>
            SoficGroups.normalizedHamming
              (((A.model n).action g)⁻¹)
              ((A.model n).action (g⁻¹))) := by
      funext n
      exact SoficGroups.normalizedHamming_comm _ _
    rw [heq]
    exact sofic_action_inverse_normalizedHamming_tendsto_zero A g
  simpa only [Fintype.card_fin] using
    (squaredPermutationEnergy_tendsto_of_normalizedHamming
      (fun n => Fin (A.model n).size) f hf0 hf1
      (fun n => (A.model n).action (g⁻¹))
      (fun n => ((A.model n).action g)⁻¹)
      (by simpa only [Fintype.card_fin] using htrue) hd)
end SoficGroups.KunPositiveWordMidrankEnergy
