-- Prove2me | solution 1 for SoficGroups.ErshovJaikinFiniteSpectral.norm_sub_starProjection_le_finiteUnitarySubgroupAverage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:54.580336+00:00
-- url     : https://prove2.me/submissions/c2d8f96e-e2a4-4e0e-93d6-57fa5bd57588

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.ErshovJaikinFiniteSpectral
open Filter Topology
universe u v
variable {G : Type u} {H : Type v} [Group G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
namespace SoficGroups.ErshovJaikinFiniteSpectral
theorem _root_.solution
    (π : SoficGroups.UnitaryRepresentation G H)
    (K : Subgroup G) [Fintype K]
    (U : Submodule ℂ H) [U.HasOrthogonalProjection]
    (x : H) (hmem : finiteUnitarySubgroupAverage π K x ∈ U) :
    ‖x - U.starProjection x‖ ≤
      ‖finiteUnitarySubgroupAverage π K x - x‖ := by
  rw [Submodule.starProjection_minimal]
  have hbound : BddBelow
      (Set.range fun z : U => ‖x - (z : H)‖) :=
    ⟨0, Set.forall_mem_range.mpr fun _ => norm_nonneg _⟩
  calc
    (⨅ z : U, ‖x - (z : H)‖) ≤
        ‖x - (⟨finiteUnitarySubgroupAverage π K x, hmem⟩ : U)‖ :=
      ciInf_le hbound _
    _ = ‖finiteUnitarySubgroupAverage π K x - x‖ :=
      norm_sub_rev _ _
end SoficGroups.ErshovJaikinFiniteSpectral
