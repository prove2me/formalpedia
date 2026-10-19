-- Prove2me | solution 1 for SoficGroups.SourceCompressionTransportCrossing.tendsto_action_inverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.698756+00:00
-- url     : https://prove2.me/submissions/69a263e9-042f-4e92-9cb5-389e0958ad3e

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_normalizedHamming_mul_left

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.SourceCompressionTransportCrossing
open Filter Topology
open scoped BigOperators
namespace SoficGroups.SourceCompressionTransportCrossing
theorem _root_.solution
    {G : Type*} [Group G] (A : SoficGroups.SoficApproximation G)
    (u : G) :
    Tendsto
      (fun n => SoficGroups.normalizedHamming
        (((A.model n).action u)⁻¹)
        ((A.model n).action (u⁻¹)))
      atTop (nhds 0) := by
  have heq :
      (fun n => SoficGroups.normalizedHamming
        (((A.model n).action u)⁻¹)
        ((A.model n).action (u⁻¹))) =
      (fun n => SoficGroups.normalizedHamming
        ((A.model n).action (u * u⁻¹))
        ((A.model n).action u * (A.model n).action (u⁻¹))) := by
    funext n
    calc
      SoficGroups.normalizedHamming
          (((A.model n).action u)⁻¹)
          ((A.model n).action (u⁻¹)) =
        SoficGroups.normalizedHamming
          ((A.model n).action u * ((A.model n).action u)⁻¹)
          ((A.model n).action u * (A.model n).action (u⁻¹)) :=
        (SoficGroups.normalizedHamming_mul_left
          ((A.model n).action u)
          (((A.model n).action u)⁻¹)
          ((A.model n).action (u⁻¹))).symm
      _ = SoficGroups.normalizedHamming
          ((A.model n).action (u * u⁻¹))
          ((A.model n).action u * (A.model n).action (u⁻¹)) := by
        simp [(A.model n).map_one]
  rw [heq]
  exact A.multiplicative u (u⁻¹)
end SoficGroups.SourceCompressionTransportCrossing
