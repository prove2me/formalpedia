-- Prove2me | solution 1 for SoficGroups.KunPositiveWordMidrankEnergy.sofic_action_inverse_normalizedHamming_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.855273+00:00
-- url     : https://prove2.me/submissions/3f02f3c4-1b29-4e50-b738-c493e83a6c84

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_normalizedHamming_mul_left

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunPositiveWordMidrankEnergy
open Filter Topology
open scoped BigOperators
namespace SoficGroups.KunPositiveWordMidrankEnergy
theorem _root_.solution
    {G : Type*} [Group G]
    (A : SoficGroups.SoficApproximation G) (g : G) :
    Tendsto
      (fun n =>
        SoficGroups.normalizedHamming
          (((A.model n).action g)⁻¹)
          ((A.model n).action (g⁻¹)))
      atTop (𝓝 0) := by
  have heq :
      (fun n =>
        SoficGroups.normalizedHamming
          (((A.model n).action g)⁻¹)
          ((A.model n).action (g⁻¹))) =
        (fun n =>
          SoficGroups.normalizedHamming
            ((A.model n).action (g * g⁻¹))
            ((A.model n).action g *
              (A.model n).action (g⁻¹))) := by
    funext n
    calc
      SoficGroups.normalizedHamming
          (((A.model n).action g)⁻¹)
          ((A.model n).action (g⁻¹)) =
        SoficGroups.normalizedHamming
          ((A.model n).action g *
            ((A.model n).action g)⁻¹)
          ((A.model n).action g *
            (A.model n).action (g⁻¹)) :=
        (SoficGroups.normalizedHamming_mul_left
          ((A.model n).action g)
          (((A.model n).action g)⁻¹)
          ((A.model n).action (g⁻¹))).symm
      _ = SoficGroups.normalizedHamming
          ((A.model n).action (g * g⁻¹))
          ((A.model n).action g *
            (A.model n).action (g⁻¹)) := by
        simp [(A.model n).map_one]
  rw [heq]
  exact A.multiplicative g (g⁻¹)
end SoficGroups.KunPositiveWordMidrankEnergy
