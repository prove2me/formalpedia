-- Prove2me | solution 1 for SoficGroups.SourceCompressionTransportCrossing.tendsto_action_conjugate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.698756+00:00
-- url     : https://prove2.me/submissions/3830987a-ab1c-4a70-bfae-f48c7c0142c2

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_normalizedHamming_comm
import Theorems.Thm_SoficGroups_normalizedHamming_nonneg
import Theorems.Thm_SoficGroups_normalizedHamming_triangle
import Theorems.Thm_SoficGroups_normalizedHamming_mul_left
import Theorems.Thm_SoficGroups_normalizedHamming_mul_right
import Theorems.Thm_SoficGroups_SourceCompressionTransportCrossing_tendsto_action_inverse

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.SourceCompressionTransportCrossing
open Filter Topology
open scoped BigOperators
namespace SoficGroups.SourceCompressionTransportCrossing
theorem _root_.solution
    {G : Type*} [Group G] (A : SoficGroups.SoficApproximation G)
    (u g : G) :
    Tendsto
      (fun n => SoficGroups.normalizedHamming
        ((A.model n).action (u * g * u⁻¹))
        ((A.model n).action u * (A.model n).action g *
          ((A.model n).action u)⁻¹))
      atTop (nhds 0) := by
  have hbound : ∀ n,
      SoficGroups.normalizedHamming
          ((A.model n).action (u * g * u⁻¹))
          ((A.model n).action u * (A.model n).action g *
            ((A.model n).action u)⁻¹) ≤
        SoficGroups.normalizedHamming
          ((A.model n).action (u * g * u⁻¹))
          ((A.model n).action (u * g) * (A.model n).action (u⁻¹)) +
        (SoficGroups.normalizedHamming
          ((A.model n).action (u * g))
          ((A.model n).action u * (A.model n).action g) +
          SoficGroups.normalizedHamming
            ((A.model n).action (u⁻¹))
            (((A.model n).action u)⁻¹)) := by
    intro n
    calc
      SoficGroups.normalizedHamming
          ((A.model n).action (u * g * u⁻¹))
          ((A.model n).action u * (A.model n).action g *
            ((A.model n).action u)⁻¹) ≤
        SoficGroups.normalizedHamming
          ((A.model n).action (u * g * u⁻¹))
          ((A.model n).action (u * g) * (A.model n).action (u⁻¹)) +
        SoficGroups.normalizedHamming
          ((A.model n).action (u * g) * (A.model n).action (u⁻¹))
          ((A.model n).action u * (A.model n).action g *
            ((A.model n).action u)⁻¹) :=
        SoficGroups.normalizedHamming_triangle _ _ _
      _ ≤ SoficGroups.normalizedHamming
          ((A.model n).action (u * g * u⁻¹))
          ((A.model n).action (u * g) * (A.model n).action (u⁻¹)) +
        (SoficGroups.normalizedHamming
          ((A.model n).action (u * g) * (A.model n).action (u⁻¹))
          (((A.model n).action u * (A.model n).action g) *
            (A.model n).action (u⁻¹)) +
          SoficGroups.normalizedHamming
            (((A.model n).action u * (A.model n).action g) *
              (A.model n).action (u⁻¹))
            (((A.model n).action u * (A.model n).action g) *
              ((A.model n).action u)⁻¹)) := by
        gcongr
        exact SoficGroups.normalizedHamming_triangle _ _ _
      _ = SoficGroups.normalizedHamming
          ((A.model n).action (u * g * u⁻¹))
          ((A.model n).action (u * g) * (A.model n).action (u⁻¹)) +
        (SoficGroups.normalizedHamming
          ((A.model n).action (u * g))
          ((A.model n).action u * (A.model n).action g) +
          SoficGroups.normalizedHamming
            ((A.model n).action (u⁻¹))
            (((A.model n).action u)⁻¹)) := by
        rw [SoficGroups.normalizedHamming_mul_right,
          SoficGroups.normalizedHamming_mul_left]
  apply squeeze_zero
    (fun n => SoficGroups.normalizedHamming_nonneg _ _) hbound
  convert (A.multiplicative (u * g) (u⁻¹)).add
    ((A.multiplicative u g).add
      (tendsto_action_inverse A u)) using 1
  · funext n
    rw [SoficGroups.normalizedHamming_comm
      ((A.model n).action (u⁻¹))
      (((A.model n).action u)⁻¹)]
  · norm_num
end SoficGroups.SourceCompressionTransportCrossing
