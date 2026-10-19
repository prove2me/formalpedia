-- Prove2me | solution 1 for SoficGroups.KunCommonRankArcInvariance.sofic_action_inverse_normalizedHamming_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.855273+00:00
-- url     : https://prove2.me/submissions/aed72989-aa09-434e-a857-6fecb5c3ade0

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_normalizedHamming_mul_left

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunCommonRankArcInvariance
open Filter Topology
open scoped BigOperators
namespace SoficGroups.KunCommonRankArcInvariance
theorem _root_.solution
    {G : Type*} [Group G]
    (A : SoficGroups.SoficApproximation G) (g : G) :
    Tendsto
      (fun n =>
        SoficGroups.normalizedHamming
          (((A.model n).action g)⁻¹)
          ((A.model n).action (g⁻¹)))
      atTop (nhds 0) := by
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
end SoficGroups.KunCommonRankArcInvariance
